// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Igor Loi - igor.loi@unibo.it                               //
//                                                                            //
// Additional contributions by:                                               //
//                 Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Design Name:    Load Store Unit                                            //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Load Store Unit, used to eliminate multiple access during  //
//                 processor stalls, and to align bytes and halfwords         //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// MODULE: cv32e40p_load_store_unit
///////////////////////////////////////////////////////////////////////////////
// Load Store Unit (LSU) - Data Memory Access and Alignment
//
// OVERVIEW:
// The LSU handles all data memory accesses (loads/stores) for the processor.
// It interfaces between the EX stage and the data memory via the OBI protocol,
// managing address generation, data alignment, sign extension, and misaligned
// access handling.
//
// KEY RESPONSIBILITIES:
// 1. Address Generation
//    - Compute effective address from operands (base + offset or base only)
//    - Handle address alignment requirements
//
// 2. Misaligned Access Handling
//    - Detect misaligned accesses (word not on 4-byte boundary, halfword on odd byte)
//    - Split misaligned accesses into two aligned memory transactions
//    - Reassemble data from multiple transactions
//
// 3. Data Alignment and Byte Lane Steering
//    - Generate byte enable signals based on data type and address
//    - Rotate store data to correct byte lanes
//    - Extract and align load data from memory response
//
// 4. Sign Extension
//    - Zero-extend unsigned loads (LBU, LHU)
//    - Sign-extend signed loads (LB, LH)
//    - Pass-through word loads (LW)
//
// 5. OBI Protocol Management
//    - Issue transaction requests to OBI interface
//    - Track outstanding transactions (up to DEPTH=2)
//    - Handle backpressure and flow control
//
// 6. Load Event Support (PULP)
//    - Signal start/finish of event load operations
//    - Used for hardware synchronization primitives
//
// PIPELINE INTEGRATION:
// - Operates across EX and WB stages
// - EX stage: Address generation, request issue, first part of misaligned access
// - WB stage: Response collection, data alignment, second part of misaligned access
// - Provides separate ready signals for EX and WB stages
//
// MISALIGNED ACCESS HANDLING:
// Word (4 bytes):
//   - Aligned: Single transaction (address[1:0] == 2'b00)
//   - Misaligned: Two transactions (address[1:0] != 2'b00)
//     * First: Upper bytes at current word
//     * Second: Lower bytes at next word (word-aligned address)
//     * Data reassembled from both responses
//
// Halfword (2 bytes):
//   - Aligned: Single transaction (address[1:0] != 2'b11)
//   - Misaligned: Two transactions (address[1:0] == 2'b11)
//     * First: Byte 0 at current word
//     * Second: Byte 1 at next word
//
// Byte (1 byte):
//   - Always aligned (single transaction)
//
// OUTSTANDING TRANSACTIONS:
// - Counter (cnt_q) tracks 0 to DEPTH (2) outstanding transactions
// - Prevents overflow by gating new requests when cnt_q >= DEPTH
// - Essential for handling misaligned accesses (need 2 sequential transactions)
//
// OBI PROTOCOL MODES:
// - PULP_OBI=0 (Standard): Multiple requests can be issued before responses arrive
//   * Better performance, allows pipelining
// - PULP_OBI=1 (Legacy): New request only when previous response arrives
//   * Simplified timing, critical path from data_rvalid_i to data_req_o
//
// TIMING:
// - Request phase: trans_valid/trans_ready handshake (issued from EX)
// - Response phase: resp_valid indicates data available (consumed in WB)
// - Minimum 1 cycle latency from request to response (OBI requirement)
// - Misaligned accesses require at least 2 cycles (two transactions)
//
///////////////////////////////////////////////////////////////////////////////

module cv32e40p_load_store_unit #(
    ///////////////////////////////////////////////////////////////////////////
    // Parameters
    ///////////////////////////////////////////////////////////////////////////
    // PULP_OBI: OBI protocol behavior mode
    //   0: Standard OBI (multiple outstanding requests allowed)
    //   1: Legacy PULP OBI (wait for response before next request)
    parameter PULP_OBI = 0
) (
    ///////////////////////////////////////////////////////////////////////////
    // Clock and Reset
    ///////////////////////////////////////////////////////////////////////////
    input logic clk,                              // System clock
    input logic rst_n,                            // Asynchronous active-low reset

    ///////////////////////////////////////////////////////////////////////////
    // Data Memory Interface (OBI Protocol)
    ///////////////////////////////////////////////////////////////////////////
    // Request phase
    output logic        data_req_o,               // Request valid
    input  logic        data_gnt_i,               // Request granted (request accepted)
    output logic [31:0] data_addr_o,              // Address (word-aligned for OBI)
    output logic        data_we_o,                // Write enable (1=store, 0=load)
    output logic [ 3:0] data_be_o,                // Byte enables (one bit per byte)
    output logic [31:0] data_wdata_o,             // Write data (for stores)
    
    // Response phase
    input logic        data_rvalid_i,             // Response valid (data available)
    input logic [31:0] data_rdata_i,              // Read data (for loads)
    
    // Error signals
    input logic data_err_i,                       // External bus error (not used yet)
    input logic data_err_pmp_i,                   // PMP access error (not used yet)

    ///////////////////////////////////////////////////////////////////////////
    // Control from EX Stage
    ///////////////////////////////////////////////////////////////////////////
    input logic        data_req_ex_i,             // Data memory request enable
    input logic        data_we_ex_i,              // Write enable (1=store, 0=load)
    input logic [ 1:0] data_type_ex_i,            // Data type: 00=word, 01=halfword, 10/11=byte
    input logic [31:0] data_wdata_ex_i,           // Write data from register file
    input logic [ 1:0] data_reg_offset_ex_i,      // Register offset for partial stores
    input logic        data_load_event_ex_i,      // Load event operation (PULP)
    input logic [ 1:0] data_sign_ext_ex_i,        // Sign extension: 00=zero, 01=sign, 10=ones
    input logic [ 5:0] data_atop_ex_i,            // Atomic operation code (not fully used)
    
    ///////////////////////////////////////////////////////////////////////////
    // Address Generation from EX Stage
    ///////////////////////////////////////////////////////////////////////////
    input logic [31:0] operand_a_ex_i,            // Base address (typically rs1)
    input logic [31:0] operand_b_ex_i,            // Offset (typically immediate)
    input logic        addr_useincr_ex_i,         // Address mode: 1=base+offset, 0=base only
    
    ///////////////////////////////////////////////////////////////////////////
    // Misaligned Access Signals
    ///////////////////////////////////////////////////////////////////////////
    input  logic data_misaligned_ex_i,            // Currently handling second part of misaligned
    output logic data_misaligned_o,               // Misaligned access detected (need 2nd transaction)

    ///////////////////////////////////////////////////////////////////////////
    // Atomic Operation Output
    ///////////////////////////////////////////////////////////////////////////
    output logic [5:0] data_atop_o,               // Atomic operation to memory (pass-through)

    ///////////////////////////////////////////////////////////////////////////
    // Load Event Signals (PULP)
    ///////////////////////////////////////////////////////////////////////////
    output logic p_elw_start_o,                   // Event load start (request issued)
    output logic p_elw_finish_o,                  // Event load finish (response received)

    ///////////////////////////////////////////////////////////////////////////
    // Data Output to EX Stage
    ///////////////////////////////////////////////////////////////////////////
    output logic [31:0] data_rdata_ex_o,          // Aligned and sign-extended load data

    ///////////////////////////////////////////////////////////////////////////
    // Pipeline Control
    ///////////////////////////////////////////////////////////////////////////
    output logic lsu_ready_ex_o,                  // LSU ready for new request in EX
    output logic lsu_ready_wb_o,                  // LSU ready (WB stage available)

    ///////////////////////////////////////////////////////////////////////////
    // Status
    ///////////////////////////////////////////////////////////////////////////
    output logic busy_o                           // LSU has outstanding transactions
);

  ///////////////////////////////////////////////////////////////////////////////
  // Constants
  ///////////////////////////////////////////////////////////////////////////////
  // DEPTH: Maximum number of outstanding OBI transactions
  // Must be >= 2 to handle misaligned accesses (which require 2 transactions)
  localparam DEPTH = 2;

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Signals
  ///////////////////////////////////////////////////////////////////////////////
  
  ///////////////////////////////////////////////////////////////////////////
  // Transaction Interface (to cv32e40p_obi_interface)
  ///////////////////////////////////////////////////////////////////////////
  // Request phase
  logic        trans_valid;                      // Transaction request valid
  logic        trans_ready;                      // Transaction request accepted
  logic [31:0] trans_addr;                       // Transaction address
  logic        trans_we;                         // Transaction write enable
  logic [ 3:0] trans_be;                         // Transaction byte enables
  logic [31:0] trans_wdata;                      // Transaction write data
  logic [ 5:0] trans_atop;                       // Transaction atomic operation

  // Response phase
  logic        resp_valid;                       // Response valid
  logic [31:0] resp_rdata;                       // Response read data
  logic        resp_err;                         // Response error (not used yet)

  ///////////////////////////////////////////////////////////////////////////
  // Outstanding Transaction Counter
  ///////////////////////////////////////////////////////////////////////////
  logic [1:0] cnt_q;                             // Current count (0 to DEPTH)
  logic [1:0] next_cnt;                          // Next count value
  logic       count_up;                          // Increment counter (request accepted)
  logic       count_down;                        // Decrement counter (response received)

  ///////////////////////////////////////////////////////////////////////////
  // Control Signals
  ///////////////////////////////////////////////////////////////////////////
  logic ctrl_update;                             // Update EX→WB pipeline registers

  ///////////////////////////////////////////////////////////////////////////
  // Address Generation
  ///////////////////////////////////////////////////////////////////////////
  logic [31:0] data_addr_int;                    // Computed effective address

  ///////////////////////////////////////////////////////////////////////////
  // EX/WB Pipeline Registers
  ///////////////////////////////////////////////////////////////////////////
  // These registers store load control information from EX to WB stage
  logic [1:0] data_type_q;                       // Registered data type
  logic [1:0] rdata_offset_q;                    // Registered address offset (for alignment)
  logic [1:0] data_sign_ext_q;                   // Registered sign extension mode
  logic       data_we_q;                         // Registered write enable
  logic       data_load_event_q;                 // Registered load event flag

  ///////////////////////////////////////////////////////////////////////////
  // Data Path Signals
  ///////////////////////////////////////////////////////////////////////////
  logic [1:0]  wdata_offset;                     // Write data rotation amount
  logic [ 3:0] data_be;                          // Byte enables
  logic [31:0] data_wdata;                       // Rotated write data

  ///////////////////////////////////////////////////////////////////////////
  // Misaligned Access Handling
  ///////////////////////////////////////////////////////////////////////////
  logic misaligned_st;                           // Currently doing second part of misaligned store
  logic [31:0] rdata_q;                          // Saved data from first part of misaligned load

  ///////////////////////////////////////////////////////////////////////////
  // Error Signals (not currently used)
  ///////////////////////////////////////////////////////////////////////////
  logic load_err_o;                              // Load PMP error
  logic store_err_o;                             // Store PMP error

  ///////////////////////////////////////////////////////////////////////////////
  // BYTE ENABLE GENERATION
  ///////////////////////////////////////////////////////////////////////////////
  // Generate byte enable signals based on:
  //   - data_type_ex_i: Word (00), halfword (01), byte (10/11)
  //   - data_addr_int[1:0]: Address alignment
  //   - misaligned_st: First or second part of misaligned access
  //
  // For misaligned accesses:
  //   - First transaction: Enable upper bytes at current word
  //   - Second transaction: Enable lower bytes at next word (word-aligned)


  ///////////////////////////////////////////////////////////////////////////////
  // BYTE ENABLE GENERATION
  ///////////////////////////////////////////////////////////////////////////////
  // Generate byte enable signals based on:
  //   - data_type_ex_i: Word (00), halfword (01), byte (10/11)
  //   - data_addr_int[1:0]: Address alignment
  //   - misaligned_st: First or second part of misaligned access
  //
  // For misaligned accesses:
  //   - First transaction: Enable upper bytes at current word
  //   - Second transaction: Enable lower bytes at next word (word-aligned)

  always_comb begin
    case (data_type_ex_i)  // Data type 00 Word, 01 Half word, 11,10 byte
      
      ///////////////////////////////////////////////////////////////////////////
      // Word Access (4 bytes)
      ///////////////////////////////////////////////////////////////////////////
      2'b00: begin
        if (misaligned_st == 1'b0) begin
          // First part of word access (or aligned word)
          case (data_addr_int[1:0])
            2'b00:   data_be = 4'b1111;          // Aligned word: all 4 bytes
            2'b01:   data_be = 4'b1110;          // Misaligned: bytes 1,2,3
            2'b10:   data_be = 4'b1100;          // Misaligned: bytes 2,3
            default: data_be = 4'b1000;          // Misaligned: byte 3 only
          endcase
        end else begin
          // Second part of misaligned word access
          case (data_addr_int[1:0])
            2'b01:   data_be = 4'b0001;          // Complete with byte 0
            2'b10:   data_be = 4'b0011;          // Complete with bytes 0,1
            2'b11:   data_be = 4'b0111;          // Complete with bytes 0,1,2
            default: data_be = 4'b0000;          // Should not occur
          endcase
        end
      end

      ///////////////////////////////////////////////////////////////////////////
      // Halfword Access (2 bytes)
      ///////////////////////////////////////////////////////////////////////////
      2'b01: begin
        if (misaligned_st == 1'b0) begin
          // First part of halfword access (or aligned halfword)
          case (data_addr_int[1:0])
            2'b00:   data_be = 4'b0011;          // Aligned at bytes 0,1
            2'b01:   data_be = 4'b0110;          // Aligned at bytes 1,2
            2'b10:   data_be = 4'b1100;          // Aligned at bytes 2,3
            default: data_be = 4'b1000;          // Misaligned: byte 3 only
          endcase
        end else begin
          // Second part of misaligned halfword access
          data_be = 4'b0001;                     // Complete with byte 0
        end
      end

      ///////////////////////////////////////////////////////////////////////////
      // Byte Access (1 byte)
      ///////////////////////////////////////////////////////////////////////////
      2'b10, 2'b11: begin
        // Byte accesses never misaligned
        case (data_addr_int[1:0])
          2'b00:   data_be = 4'b0001;            // Byte 0
          2'b01:   data_be = 4'b0010;            // Byte 1
          2'b10:   data_be = 4'b0100;            // Byte 2
          default: data_be = 4'b1000;            // Byte 3
        endcase
      end
    endcase
  end

  ///////////////////////////////////////////////////////////////////////////////
  // WRITE DATA ROTATION
  ///////////////////////////////////////////////////////////////////////////////
  // Rotate write data to align with byte enables
  // Handles register offset for partial register stores
  //
  // wdata_offset determines rotation:
  //   00: No rotation (data already aligned)
  //   01: Rotate left 1 byte  (move bits 23:0 to 31:8)
  //   10: Rotate left 2 bytes (move bits 15:0 to 31:16)
  //   11: Rotate left 3 bytes (move bits  7:0 to 31:24)

  assign wdata_offset = data_addr_int[1:0] - data_reg_offset_ex_i[1:0];
  always_comb begin
    case (wdata_offset)
      2'b00: data_wdata = data_wdata_ex_i[31:0];                              // No rotation
      2'b01: data_wdata = {data_wdata_ex_i[23:0], data_wdata_ex_i[31:24]};   // Rotate 1 byte
      2'b10: data_wdata = {data_wdata_ex_i[15:0], data_wdata_ex_i[31:16]};   // Rotate 2 bytes
      2'b11: data_wdata = {data_wdata_ex_i[7:0], data_wdata_ex_i[31:8]};     // Rotate 3 bytes
    endcase
  end


  ///////////////////////////////////////////////////////////////////////////////
  // EX/WB PIPELINE REGISTERS
  ///////////////////////////////////////////////////////////////////////////////
  // Store load control information from EX to WB stage
  // Updated when LSU accepts a new request (ctrl_update)
  //
  // These registers allow the WB stage to:
  //   - Know what type of load to expect
  //   - Properly align and sign-extend the response data
  //   - Track load events

  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      data_type_q       <= '0;
      rdata_offset_q    <= '0;
      data_sign_ext_q   <= '0;
      data_we_q         <= 1'b0;
      data_load_event_q <= 1'b0;
    end
    else if (ctrl_update) // Request was granted, moving to WB stage
    begin
      data_type_q       <= data_type_ex_i;       // Store data type
      rdata_offset_q    <= data_addr_int[1:0];   // Store address offset (for alignment)
      data_sign_ext_q   <= data_sign_ext_ex_i;   // Store sign extension mode
      data_we_q         <= data_we_ex_i;         // Store write enable (0=load)
      data_load_event_q <= data_load_event_ex_i; // Store load event flag
    end
  end

  ///////////////////////////////////////////////////////////////////////////////
  // LOAD EVENT SIGNALING (PULP)
  ///////////////////////////////////////////////////////////////////////////////
  // Track start and finish of event load operations
  // Used for hardware synchronization primitives
  
  // Load event starts when request is sent and finishes when (final) rvalid is received
  assign p_elw_start_o  = data_load_event_ex_i && data_req_o;
  assign p_elw_finish_o = data_load_event_q && data_rvalid_i && !data_misaligned_ex_i;

  ////////////////////////////////////////////////////////////////////////
  //  ____  _               _____      _                 _              //
  // / ___|(_) __ _ _ __   | ____|_  _| |_ ___ _ __  ___(_) ___  _ __   //
  // \___ \| |/ _` | '_ \  |  _| \ \/ / __/ _ \ '_ \/ __| |/ _ \| '_ \  //
  //  ___) | | (_| | | | | | |___ >  <| ||  __/ | | \__ \ | (_) | | | | //
  // |____/|_|\__, |_| |_| |_____/_/\_\\__\___|_| |_|___/_|\___/|_| |_| //
  //          |___/                                                     //
  ////////////////////////////////////////////////////////////////////////

  ///////////////////////////////////////////////////////////////////////////////
  // READ DATA ALIGNMENT AND SIGN EXTENSION
  ///////////////////////////////////////////////////////////////////////////////
  // Process load data based on:
  //   - data_type_q: Word, halfword, or byte
  //   - rdata_offset_q: Address alignment (which byte lanes contain data)
  //   - data_sign_ext_q: Zero extend, sign extend, or ones extend
  //
  // For misaligned loads:
  //   - First response: Save in rdata_q
  //   - Second response: Combine with rdata_q to form complete value
  //
  // Three-stage process:
  //   1. Word alignment (rdata_w_ext): Handle misaligned words
  //   2. Type-specific alignment: Extract halfword or byte from aligned word
  //   3. Sign/zero extension: Extend to 32 bits

  logic [31:0] data_rdata_ext;                   // Final aligned and extended data

  logic [31:0] rdata_w_ext;                      // Word alignment (misaligned assembly)
  logic [31:0] rdata_h_ext;                      // Halfword extraction and extension
  logic [31:0] rdata_b_ext;                      // Byte extraction and extension

  ///////////////////////////////////////////////////////////////////////////
  // Word Alignment
  ///////////////////////////////////////////////////////////////////////////
  // Assemble complete word from current and saved responses
  // For aligned words, use resp_rdata directly
  // For misaligned words, combine bytes from resp_rdata and rdata_q

  always_comb begin
    case (rdata_offset_q)
      2'b00: rdata_w_ext = resp_rdata[31:0];                        // Aligned word
      2'b01: rdata_w_ext = {resp_rdata[7:0], rdata_q[31:8]};        // Combine: [7:0] + saved[31:8]
      2'b10: rdata_w_ext = {resp_rdata[15:0], rdata_q[31:16]};      // Combine: [15:0] + saved[31:16]
      2'b11: rdata_w_ext = {resp_rdata[23:0], rdata_q[31:24]};      // Combine: [23:0] + saved[31:24]
    endcase
  end

  ///////////////////////////////////////////////////////////////////////////
  // Halfword Extraction and Sign Extension
  ///////////////////////////////////////////////////////////////////////////
  // Extract 16-bit halfword from correct byte lanes
  // Apply sign or zero extension to 32 bits
  //
  // data_sign_ext_q:
  //   00: Zero extend (LHU)
  //   01: Sign extend (LH)
  //   10: Ones extend (special case)

  always_comb begin
    case (rdata_offset_q)
      2'b00: begin
        // Halfword at bytes 0-1
        if (data_sign_ext_q == 2'b00) rdata_h_ext = {16'h0000, resp_rdata[15:0]};
        else if (data_sign_ext_q == 2'b10) rdata_h_ext = {16'hffff, resp_rdata[15:0]};
        else rdata_h_ext = {{16{resp_rdata[15]}}, resp_rdata[15:0]};
      end

      2'b01: begin
        // Halfword at bytes 1-2
        if (data_sign_ext_q == 2'b00) rdata_h_ext = {16'h0000, resp_rdata[23:8]};
        else if (data_sign_ext_q == 2'b10) rdata_h_ext = {16'hffff, resp_rdata[23:8]};
        else rdata_h_ext = {{16{resp_rdata[23]}}, resp_rdata[23:8]};
      end

      2'b10: begin
        // Halfword at bytes 2-3
        if (data_sign_ext_q == 2'b00) rdata_h_ext = {16'h0000, resp_rdata[31:16]};
        else if (data_sign_ext_q == 2'b10) rdata_h_ext = {16'hffff, resp_rdata[31:16]};
        else rdata_h_ext = {{16{resp_rdata[31]}}, resp_rdata[31:16]};
      end

      2'b11: begin
        // Misaligned halfword: byte 3 from current word, byte 0 from saved word
        if (data_sign_ext_q == 2'b00)
          rdata_h_ext = {16'h0000, resp_rdata[7:0], rdata_q[31:24]};
        else if (data_sign_ext_q == 2'b10)
          rdata_h_ext = {16'hffff, resp_rdata[7:0], rdata_q[31:24]};
        else rdata_h_ext = {{16{resp_rdata[7]}}, resp_rdata[7:0], rdata_q[31:24]};
      end
    endcase
  end

  ///////////////////////////////////////////////////////////////////////////
  // Byte Extraction and Sign Extension
  ///////////////////////////////////////////////////////////////////////////
  // Extract 8-bit byte from correct byte lane
  // Apply sign or zero extension to 32 bits
  //
  // data_sign_ext_q:
  //   00: Zero extend (LBU)
  //   01: Sign extend (LB)
  //   10: Ones extend (special case)

  always_comb begin
    case (rdata_offset_q)
      2'b00: begin
        // Byte 0
        if (data_sign_ext_q == 2'b00) rdata_b_ext = {24'h00_0000, resp_rdata[7:0]};
        else if (data_sign_ext_q == 2'b10) rdata_b_ext = {24'hff_ffff, resp_rdata[7:0]};
        else rdata_b_ext = {{24{resp_rdata[7]}}, resp_rdata[7:0]};
      end

      2'b01: begin
        // Byte 1
        if (data_sign_ext_q == 2'b00) rdata_b_ext = {24'h00_0000, resp_rdata[15:8]};
        else if (data_sign_ext_q == 2'b10) rdata_b_ext = {24'hff_ffff, resp_rdata[15:8]};
        else rdata_b_ext = {{24{resp_rdata[15]}}, resp_rdata[15:8]};
      end

      2'b10: begin
        // Byte 2
        if (data_sign_ext_q == 2'b00) rdata_b_ext = {24'h00_0000, resp_rdata[23:16]};
        else if (data_sign_ext_q == 2'b10) rdata_b_ext = {24'hff_ffff, resp_rdata[23:16]};
        else rdata_b_ext = {{24{resp_rdata[23]}}, resp_rdata[23:16]};
      end

      2'b11: begin
        // Byte 3
        if (data_sign_ext_q == 2'b00) rdata_b_ext = {24'h00_0000, resp_rdata[31:24]};
        else if (data_sign_ext_q == 2'b10) rdata_b_ext = {24'hff_ffff, resp_rdata[31:24]};
        else rdata_b_ext = {{24{resp_rdata[31]}}, resp_rdata[31:24]};
      end
    endcase
  end

  ///////////////////////////////////////////////////////////////////////////
  // Data Type Selection
  ///////////////////////////////////////////////////////////////////////////
  // Select final result based on data type
  always_comb begin
    case (data_type_q)
      2'b00:        data_rdata_ext = rdata_w_ext;  // Word
      2'b01:        data_rdata_ext = rdata_h_ext;  // Halfword
      2'b10, 2'b11: data_rdata_ext = rdata_b_ext;  // Byte
    endcase
  end

  ///////////////////////////////////////////////////////////////////////////
  // Response Data Register
  ///////////////////////////////////////////////////////////////////////////
  // Save first part of misaligned load or hold final result
  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      rdata_q <= '0;
    end else begin
      if (resp_valid && (~data_we_q)) begin
        // Load operation response received
        if ((data_misaligned_ex_i == 1'b1) || (data_misaligned_o == 1'b1)) 
          // Misaligned load: save raw response for combining in second transaction
          rdata_q <= resp_rdata;
        else 
          // Aligned load: save aligned/extended result
          rdata_q <= data_rdata_ext;
      end
    end
  end

  ///////////////////////////////////////////////////////////////////////////
  // Data Output to EX Stage
  ///////////////////////////////////////////////////////////////////////////
  // Provide current response or saved data
  assign data_rdata_ex_o = (resp_valid == 1'b1) ? data_rdata_ext : rdata_q;

  ///////////////////////////////////////////////////////////////////////////////
  // MISALIGNED ACCESS FLAG
  ///////////////////////////////////////////////////////////////////////////////
  // Track whether currently handling second part of misaligned access
  assign misaligned_st   = data_misaligned_ex_i;

  ///////////////////////////////////////////////////////////////////////////////
  // ERROR SIGNALS (not currently used)
  ///////////////////////////////////////////////////////////////////////////////
  // PMP errors not fully supported yet
  // Note: PMP is not fully supported at the moment (not even if USE_PMP = 1)
  assign load_err_o      = data_gnt_i && data_err_pmp_i && ~data_we_o;
  assign store_err_o     = data_gnt_i && data_err_pmp_i && data_we_o;


  ///////////////////////////////////////////////////////////////////////////////
  // MISALIGNED ACCESS DETECTION
  ///////////////////////////////////////////////////////////////////////////////
  // Detect when an access requires a second memory transaction
  // Signals to controller to hold pipeline for second transaction
  //
  // Misaligned conditions:
  //   - Word: address[1:0] != 2'b00
  //   - Halfword: address[1:0] == 2'b11
  //   - Byte: never misaligned

  always_comb begin
    data_misaligned_o = 1'b0;

    if ((data_req_ex_i == 1'b1) && (data_misaligned_ex_i == 1'b0)) begin
      case (data_type_ex_i)
        2'b00: // Word
        begin
          // Misaligned if not on 4-byte boundary
          if (data_addr_int[1:0] != 2'b00) data_misaligned_o = 1'b1;
        end
        2'b01: // Halfword
        begin
          // Misaligned if spans word boundary (byte 3 → byte 0 of next word)
          if (data_addr_int[1:0] == 2'b11) data_misaligned_o = 1'b1;
        end
      endcase
    end
  end

  ///////////////////////////////////////////////////////////////////////////////
  // ADDRESS GENERATION
  ///////////////////////////////////////////////////////////////////////////////
  // Compute effective address from operands
  //   - addr_useincr_ex_i=1: base + offset (e.g., rs1 + imm for loads/stores)
  //   - addr_useincr_ex_i=0: base only (e.g., rs1 for indirect jumps)
  assign data_addr_int = (addr_useincr_ex_i) ? (operand_a_ex_i + operand_b_ex_i) : operand_a_ex_i;

  ///////////////////////////////////////////////////////////////////////////////
  // BUSY STATUS
  ///////////////////////////////////////////////////////////////////////////////
  // LSU busy if any outstanding transactions or new request being issued
  assign busy_o = (cnt_q != 2'b00) || trans_valid;

  //////////////////////////////////////////////////////////////////////////////
  // TRANSACTION REQUEST GENERATION
  //////////////////////////////////////////////////////////////////////////////
  // Issue transaction requests to OBI interface
  //
  // Assumptions:
  //   - Response arrives at least 1 cycle after request
  //   - OBI protocol ensures no response without prior grant
  //
  // Request conditions:
  //   - EX stage has data request (data_req_ex_i)
  //   - Outstanding transaction count < DEPTH (prevent overflow)
  //
  // Address handling:
  //   - For second part of misaligned access: Force word-aligned address
  //     (LSB of data_be will indicate which bytes to access)
  //   - For normal access: Use computed address directly
  //
  // Transaction valid generation differs by OBI mode:
  //   - PULP_OBI=0 (Standard): Issue request if space available
  //   - PULP_OBI=1 (Legacy): Also require previous response (timing path)
  //////////////////////////////////////////////////////////////////////////////

  // For last phase of misaligned transfer the address needs to be word aligned (as LSB of data_be will be set)
  assign trans_addr = data_misaligned_ex_i ? {data_addr_int[31:2], 2'b00} : data_addr_int;
  assign trans_we = data_we_ex_i;
  assign trans_be = data_be;
  assign trans_wdata = data_wdata;
  assign trans_atop = data_atop_ex_i;

  // Transaction request generation
  generate
    if (PULP_OBI == 0) begin : gen_no_pulp_obi
      ///////////////////////////////////////////////////////////////////////////
      // Standard OBI Protocol
      ///////////////////////////////////////////////////////////////////////////
      // OBI compatible (avoids combinatorial path from data_rvalid_i to data_req_o).
      // Multiple trans_* transactions can be issued (and accepted) before a response
      // (resp_*) is received.
      // 
      // Better performance: Allows pipelining of multiple requests
      assign trans_valid = data_req_ex_i && (cnt_q < DEPTH);
    end else begin : gen_pulp_obi
      ///////////////////////////////////////////////////////////////////////////
      // Legacy PULP OBI Protocol
      ///////////////////////////////////////////////////////////////////////////
      // Legacy PULP OBI behavior, i.e. only issue subsequent transaction if preceding transfer
      // is about to finish (re-introducing timing critical path from data_rvalid_i to data_req_o)
      // 
      // Simplified timing at cost of performance
      assign trans_valid = (cnt_q == 2'b00) ? data_req_ex_i && (cnt_q < DEPTH) :
                                              data_req_ex_i && (cnt_q < DEPTH) && resp_valid;
    end
  endgenerate

  ///////////////////////////////////////////////////////////////////////////////
  // PIPELINE READY SIGNALS
  ///////////////////////////////////////////////////////////////////////////////
  // Control when EX and WB stages can accept new instructions
  //
  // Two-stage operation:
  //   - EX stage: Issue request, generate address/data, detect misalignment
  //   - WB stage: Collect response, align data, write to register file
  //
  // Ready logic ensures:
  //   - EX and WB advance in lock-step (no instruction overtaking)
  //   - Misaligned accesses hold EX until both transactions complete
  //   - Backpressure propagates correctly through pipeline

  ///////////////////////////////////////////////////////////////////////////
  // WB Stage Ready
  ///////////////////////////////////////////////////////////////////////////
  // LSU WB stage is ready if it is not being used (i.e. no outstanding transfers, cnt_q = 0),
  // or if WB stage is being used and the awaited response arrives (resp_valid).
  assign lsu_ready_wb_o = (cnt_q == 2'b00) ? 1'b1 : resp_valid;

  ///////////////////////////////////////////////////////////////////////////
  // EX Stage Ready
  ///////////////////////////////////////////////////////////////////////////
  // LSU EX stage readiness requires two criteria to be met:
  // 
  // 1. A data request (data_req_ex_i) has been forwarded/accepted (trans_valid && trans_ready)
  // 2. The LSU WB stage is available such that EX and WB can be updated in lock step
  //
  // Cases:
  //   - No request: Always ready (default)
  //   - cnt_q == 0 (WB idle): Ready when request accepted
  //   - cnt_q == 1 (WB busy): Ready when WB completes AND new request accepted (lock-step)
  //   - cnt_q >= 2: Ready when WB completes (can't issue more requests)

  assign lsu_ready_ex_o = (data_req_ex_i == 1'b0) ? 1'b1 :
                          (cnt_q == 2'b00) ? (              trans_valid && trans_ready) : 
                          (cnt_q == 2'b01) ? (resp_valid && trans_valid && trans_ready) : 
                                              resp_valid;

  ///////////////////////////////////////////////////////////////////////////
  // Control Update Signal
  ///////////////////////////////////////////////////////////////////////////
  // Update signals for EX/WB registers (when EX has valid data itself and is ready for next)
  assign ctrl_update = lsu_ready_ex_o && data_req_ex_i;


  //////////////////////////////////////////////////////////////////////////////
  // OUTSTANDING TRANSACTION COUNTER
  //////////////////////////////////////////////////////////////////////////////
  // Tracks number of issued requests awaiting responses (0 to DEPTH)
  // 
  // Prevents:
  //   - Overflow: Limit requests to DEPTH (enforced by trans_valid gating)
  //   - Underflow: OBI protocol guarantees resp_valid only after request grant
  //
  // Counter operations:
  //   - Increment (count_up): Transaction request accepted (trans_valid && trans_ready)
  //   - Decrement (count_down): Transaction response received (resp_valid)
  //   - Both can occur simultaneously (cnt_q unchanged)
  //
  // States:
  //   - cnt_q == 0: No outstanding transactions, WB idle
  //   - cnt_q == 1: One outstanding transaction, WB will be busy
  //   - cnt_q == 2 (DEPTH): Maximum outstanding, no new requests allowed
  //////////////////////////////////////////////////////////////////////////////

  assign count_up = trans_valid && trans_ready;  // Increment upon accepted transfer request
  assign count_down = resp_valid;  // Decrement upon accepted transfer response

  always_comb begin
    unique case ({
      count_up, count_down
    })
      2'b00: begin
        // No change
        next_cnt = cnt_q;
      end
      2'b01: begin
        // Response only: decrement
        next_cnt = cnt_q - 1'b1;
      end
      2'b10: begin
        // Request only: increment
        next_cnt = cnt_q + 1'b1;
      end
      2'b11: begin
        // Both request and response: no change
        next_cnt = cnt_q;
      end
    endcase
  end


  //////////////////////////////////////////////////////////////////////////////
  // COUNTER REGISTER
  //////////////////////////////////////////////////////////////////////////////
  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      cnt_q <= '0;
    end else begin
      cnt_q <= next_cnt;
    end
  end


  //////////////////////////////////////////////////////////////////////////////
  // OBI INTERFACE INSTANTIATION
  //////////////////////////////////////////////////////////////////////////////
  // Adapter between transaction interface and OBI protocol
  //
  // Transaction interface (internal to LSU):
  //   - trans_valid/trans_ready: Handshake (valid can stay high until ready)
  //   - trans_addr/we/be/wdata/atop: Request attributes
  //   - resp_valid: Response indication
  //   - resp_rdata: Response data
  //
  // OBI interface (external memory bus):
  //   - obi_req_o/obi_gnt_i: Request handshake
  //   - obi_addr_o/obi_we_o/obi_be_o/obi_wdata_o/obi_atop_o: Request phase
  //   - obi_rvalid_i/obi_rdata_i/obi_err_i: Response phase
  //
  // TRANS_STABLE parameter:
  //   - 1: Transaction signals held stable until accepted (required for correct operation)
  //////////////////////////////////////////////////////////////////////////////

  cv32e40p_obi_interface #(
      .TRANS_STABLE(1)
  ) data_obi_i (
      // Clock and reset
      .clk  (clk),
      .rst_n(rst_n),

      // Transaction request interface (from LSU)
      .trans_valid_i(trans_valid),
      .trans_ready_o(trans_ready),
      .trans_addr_i (trans_addr),
      .trans_we_i   (trans_we),
      .trans_be_i   (trans_be),
      .trans_wdata_i(trans_wdata),
      .trans_atop_i (trans_atop),

      // Transaction response interface (to LSU)
      .resp_valid_o(resp_valid),
      .resp_rdata_o(resp_rdata),
      .resp_err_o  (resp_err),                   // Unused for now

      // OBI interface (external memory bus)
      .obi_req_o   (data_req_o),
      .obi_gnt_i   (data_gnt_i),
      .obi_addr_o  (data_addr_o),
      .obi_we_o    (data_we_o),
      .obi_be_o    (data_be_o),
      .obi_wdata_o (data_wdata_o),
      .obi_atop_o  (data_atop_o),                // Not (yet) defined in OBI 1.0 spec
      .obi_rdata_i (data_rdata_i),
      .obi_rvalid_i(data_rvalid_i),
      .obi_err_i   (data_err_i)                  // External bus error (validity defined by obi_rvalid_i)
  );


  //////////////////////////////////////////////////////////////////////////////
  // ASSERTIONS
  //////////////////////////////////////////////////////////////////////////////

`ifdef CV32E40P_ASSERT_ON

  ///////////////////////////////////////////////////////////////////////////
  // No Errors
  ///////////////////////////////////////////////////////////////////////////
  // External data bus errors are not supported yet. PMP errors are not supported yet.
  // 
  // Note: Once PMP is re-introduced please consider to make data_err_pmp_i a 'data' signal
  // that is qualified with data_req_o && data_gnt_i (instead of suppressing data_gnt_i 
  // as is currently done. This will keep the data_req_o/data_gnt_i protocol intact.
  //
  // JUST RE-ENABLING the PMP VIA ITS USE_PMP LOCALPARAM WILL NOT WORK AS DATA_ERR_PMP_I 
  // NO LONGER FEEDS INTO LSU_READY_EX_O.

  property p_no_error;
    @(posedge clk) (1'b1) |-> ((data_err_i == 1'b0) && (data_err_pmp_i == 1'b0));
  endproperty

  a_no_error :
  assert property (p_no_error);

  ///////////////////////////////////////////////////////////////////////////
  // Transaction Counter Bounds
  ///////////////////////////////////////////////////////////////////////////
  // Check that outstanding transaction count will not overflow DEPTH
  property p_no_transaction_count_overflow_0;
    @(posedge clk) (1'b1) |-> (cnt_q <= DEPTH);
  endproperty

  a_no_transaction_count_overflow_0 :
  assert property (p_no_transaction_count_overflow_0);

  property p_no_transaction_count_overflow_1;
    @(posedge clk) (cnt_q == DEPTH) |-> (!count_up || count_down);
  endproperty

  a_no_transaction_count_overflow_1 :
  assert property (p_no_transaction_count_overflow_1);

  ///////////////////////////////////////////////////////////////////////////
  // No Spurious Responses
  ///////////////////////////////////////////////////////////////////////////
  // Check that an rvalid only occurs when there are outstanding transaction(s)
  property p_no_spurious_rvalid;
    @(posedge clk) (data_rvalid_i == 1'b1) |-> (cnt_q > 0);
  endproperty

  a_no_spurious_rvalid :
  assert property (p_no_spurious_rvalid);

  ///////////////////////////////////////////////////////////////////////////
  // Request Phase Signal Integrity
  ///////////////////////////////////////////////////////////////////////////
  // Check that the address/we/be/atop does not contain X when request is sent
  property p_address_phase_signals_defined;
    @(posedge clk) (data_req_o == 1'b1) |-> (!($isunknown(
        data_addr_o
    ) || $isunknown(
        data_we_o
    ) || $isunknown(
        data_be_o
    ) || $isunknown(
        data_atop_o
    )));
  endproperty

  a_address_phase_signals_defined :
  assert property (p_address_phase_signals_defined);

`endif

endmodule
