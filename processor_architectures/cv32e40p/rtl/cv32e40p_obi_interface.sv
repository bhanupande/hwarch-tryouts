// Copyright 2020 Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License").
//
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
//
// You may obtain a copy of the License at:
//
//     https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS
// OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
//
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Arjan Bink - arjan.bink@silabs.com                         //
//                                                                            //
// Design Name:    OBI (Open Bus Interface)                                   //
// Project Name:   CV32E40P                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Open Bus Interface adapter. Translates transaction request //
//                 on the trans_* interface into an OBI A channel transfer.   //
//                 The OBI R channel transfer translated (i.e. passed on) as  //
//                 a transaction response on the resp_* interface.            //
//                                                                            //
//                 This adapter does not limit the number of outstanding      //
//                 OBI transactions in any way.                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Module: cv32e40p_obi_interface
///////////////////////////////////////////////////////////////////////////////
// 
// FUNCTION:
//   Protocol adapter between CV32E40P's internal transaction interface and
//   the Open Bus Interface (OBI) standard. Ensures OBI protocol compliance
//   for address phase signals while allowing multiple outstanding transactions.
//
// OBI PROTOCOL OVERVIEW:
//   OBI is a simple, latency-insensitive bus protocol with separate address
//   and response channels. Key features:
//   - Address (A) Channel: req, gnt handshake for requests
//   - Response (R) Channel: rvalid indicates response availability
//   - Out-of-order responses: Supported via transaction IDs (not used here)
//   - Multiple outstanding: No inherent limit on pending transactions
//
// A CHANNEL PROTOCOL:
//   - Master asserts req with address, command, data
//   - Slave asserts gnt when ready to accept (may be same cycle)
//   - Address phase signals MUST remain stable until gnt
//   - After gnt, master can immediately issue new request
//
// R CHANNEL PROTOCOL:
//   - Slave asserts rvalid when response ready
//   - Master samples rdata, err on rvalid
//   - No backpressure: Master must be ready to accept response
//   - Responses may arrive in any order relative to requests
//
// TRANS_STABLE PARAMETER:
//   Controls whether input transaction signals are assumed stable:
//   
//   TRANS_STABLE = 1 (Stable Mode):
//     - Transaction interface signals guaranteed stable by upstream logic
//     - No internal registers needed
//     - Zero latency pass-through
//     - Smaller area (no FSM, no registers)
//     - Use when: LSU or IF stage holds signals stable until trans_ready_o
//   
//   TRANS_STABLE = 0 (Unstable Mode):
//     - Transaction signals may change before trans_ready_o
//     - Internal FSM and registers ensure OBI compliance
//     - Captures transaction on first cycle, holds until gnt
//     - Slightly larger area (FSM + 6 registers)
//     - Use when: Upstream logic cannot guarantee stability
//
// FSM STATES (when TRANS_STABLE = 0):
//   TRANSPARENT:
//     - Pass transaction signals directly to OBI
//     - Monitor for non-granted requests
//     - Transition to REGISTERED if req && !gnt
//   
//   REGISTERED:
//     - Drive OBI from internal registers (stable signals)
//     - Hold req high (never retract)
//     - Transition to TRANSPARENT on gnt
//
// OUTSTANDING TRANSACTIONS:
//   This module does NOT limit outstanding transactions. It's the
//   responsibility of upstream logic (LSU, IF stage) to track how many
//   transactions are pending and avoid overflow. OBI slaves must handle
//   the maximum number of outstanding transactions they receive.
//
// TIMING:
//   - Address phase: 0 cycles (TRANS_STABLE=1) or 1 cycle capture latency
//   - Response: Pass-through (0 cycles from rvalid to resp_valid_o)
//   - Critical path: Transaction signals → OBI outputs (combinational)
//
// USE CASES:
//   - Instruction fetch interface (typically TRANS_STABLE=0)
//   - Data memory interface (typically TRANS_STABLE=0)
//   - Peripheral access (TRANS_STABLE depends on timing requirements)
//
///////////////////////////////////////////////////////////////////////////////

module cv32e40p_obi_interface #(
    // TRANS_STABLE: Stability guarantee for transaction interface
    // 0 = Signals may change before trans_ready_o (use FSM + registers)
    // 1 = Signals guaranteed stable until trans_ready_o (pass-through)
    parameter TRANS_STABLE =  0
) (
    input logic clk,     // Clock
    input logic rst_n,   // Active-low reset

    ///////////////////////////////////////////////////////////////////////////
    // Transaction Request Interface (from LSU/IF stage)
    ///////////////////////////////////////////////////////////////////////////
    input logic trans_valid_i,      // Transaction request valid
    output logic trans_ready_o,     // Transaction accepted (can change request)
    input logic [31:0] trans_addr_i,// Transaction address
    input logic trans_we_i,         // Write enable (1=write, 0=read)
    input logic [3:0] trans_be_i,   // Byte enables (which bytes to access)
    input logic [31:0] trans_wdata_i,// Write data
    input  logic  [5:0] trans_atop_i,// Atomic operation (future extension, not OBI 1.0)

    ///////////////////////////////////////////////////////////////////////////
    // Transaction Response Interface (to LSU/IF stage)
    ///////////////////////////////////////////////////////////////////////////
    output logic resp_valid_o,      // Response valid (consumer must accept immediately)
    output logic [31:0] resp_rdata_o,// Read data response
    output logic resp_err_o,        // Error response (bus error, decode error, etc.)

    ///////////////////////////////////////////////////////////////////////////
    // OBI Master Interface (to memory/bus fabric)
    ///////////////////////////////////////////////////////////////////////////
    // OBI A Channel (Address/Request Phase)
    output logic        obi_req_o,     // Request valid
    input  logic        obi_gnt_i,     // Grant (slave accepts request)
    output logic [31:0] obi_addr_o,    // Address
    output logic        obi_we_o,      // Write enable
    output logic [ 3:0] obi_be_o,      // Byte enable
    output logic [31:0] obi_wdata_o,   // Write data
    output logic [ 5:0] obi_atop_o,    // Atomic operation
    
    // OBI R Channel (Response Phase)
    input  logic [31:0] obi_rdata_i,   // Read data
    input  logic        obi_rvalid_i,  // Response valid
    input  logic        obi_err_i      // Error response
);


  // FSM state encoding
  enum logic {
    TRANSPARENT,  // Pass-through mode: transaction signals → OBI directly
    REGISTERED    // Registered mode: drive OBI from internal registers
  }
      state_q, next_state;

  ///////////////////////////////////////////////////////////////////////////////
  // OBI R Channel (Response Phase)
  ///////////////////////////////////////////////////////////////////////////////
  // Response channel is always pass-through (no buffering)
  // Consumer MUST be ready to accept response when resp_valid_o asserts
  // This is guaranteed by CV32E40P's LSU and IF stage design

  // The OBI R channel signals are passed on directly on the transaction response
  // interface (resp_*). It is assumed that the consumer of the transaction response
  // is always receptive when resp_valid_o = 1 (otherwise a response would get dropped)

  assign resp_valid_o = obi_rvalid_i;  // Response valid from OBI slave
  assign resp_rdata_o = obi_rdata_i;   // Read data from OBI slave
  assign resp_err_o   = obi_err_i;     // Error flag from OBI slave


  ///////////////////////////////////////////////////////////////////////////////
  // OBI A Channel (Address/Request Phase)
  ///////////////////////////////////////////////////////////////////////////////
  // Behavior depends on TRANS_STABLE parameter:
  //   TRANS_STABLE=1: Zero-latency pass-through
  //   TRANS_STABLE=0: FSM-based stable signal generation

  generate
    //-------------------------------------------------------------------------
    // Configuration 1: TRANS_STABLE = 1 (Stable Transaction Signals)
    //-------------------------------------------------------------------------
    // Assumption: Upstream logic guarantees trans_* signals remain stable
    //             from trans_valid_i assertion until trans_ready_o response
    // Behavior: Direct connection (combinational pass-through)
    // Advantages: Zero latency, minimal area (no registers, no FSM)
    
    if (TRANS_STABLE) begin : gen_trans_stable

      // If the incoming transaction itself is stable, then it satisfies the OBI protocol
      // and signals can be passed to/from OBI directly.
      assign obi_req_o     = trans_valid_i;   // Request when transaction valid
      assign obi_addr_o    = trans_addr_i;    // Address pass-through
      assign obi_we_o      = trans_we_i;      // Write enable pass-through
      assign obi_be_o      = trans_be_i;      // Byte enable pass-through
      assign obi_wdata_o   = trans_wdata_i;   // Write data pass-through
      assign obi_atop_o    = trans_atop_i;    // Atomic operation pass-through

      assign trans_ready_o = obi_gnt_i;       // Ready when OBI grants

      // FSM not used in this mode
      assign state_q       = TRANSPARENT;
      assign next_state    = TRANSPARENT;
      
    //-------------------------------------------------------------------------
    // Configuration 2: TRANS_STABLE = 0 (Potentially Unstable Signals)
    //-------------------------------------------------------------------------
    // Assumption: trans_* signals MAY change before trans_ready_o
    // Behavior: Capture and hold transaction in registers if not immediately granted
    // Advantages: Works with any upstream logic, ensures OBI protocol compliance
    
    end else begin : gen_no_trans_stable

      // OBI A channel registers (to keep A channel stable)
      logic [31:0] obi_addr_q;    // Captured address
      logic        obi_we_q;      // Captured write enable
      logic [ 3:0] obi_be_q;      // Captured byte enable
      logic [31:0] obi_wdata_q;   // Captured write data
      logic [ 5:0] obi_atop_q;    // Captured atomic operation

      // If the incoming transaction itself is not stable; use an FSM to make sure that
      // the OBI address phase signals are kept stable during non-granted requests.

      ///////////////////////////////////////////////////////////////////////////
      // OBI FSM State Machine
      ///////////////////////////////////////////////////////////////////////////
      // Controls whether OBI A channel is driven from inputs or registers
      // Ensures OBI protocol compliance (stable signals until grant)

      // FSM (state_q, next_state) to control OBI A channel signals.

      always_comb begin
        next_state = state_q;  // Default: hold current state

        case (state_q)

          //-------------------------------------------------------------------
          // TRANSPARENT State
          //-------------------------------------------------------------------
          // Normal operation: Pass transaction signals directly to OBI
          // Monitor for non-granted requests to trigger capture
          
          // Default (transparent) state. Transaction requests are passed directly onto the OBI A channel.
          TRANSPARENT: begin
            if (obi_req_o && !obi_gnt_i) begin
              // OBI request not immediately granted. Move to REGISTERED state such that OBI address phase
              // signals can be kept stable while the transaction request (trans_*) can possibly change.
              // This ensures OBI protocol compliance even if upstream changes trans_* signals
              next_state = REGISTERED;
            end
          end  // case: TRANSPARENT

          //-------------------------------------------------------------------
          // REGISTERED State
          //-------------------------------------------------------------------
          // Holding mode: Drive OBI from internal registers
          // Keep request asserted until grant received
          
          // Registered state. OBI address phase signals are kept stable (driven from registers).
          REGISTERED: begin
            if (obi_gnt_i) begin
              // Received grant. Move back to TRANSPARENT state such that next transaction request can be passed on.
              // This allows accepting a new transaction in the next cycle
              next_state = TRANSPARENT;
            end
          end  // case: REGISTERED

        endcase
      end

      ///////////////////////////////////////////////////////////////////////////
      // OBI Output Muxing
      ///////////////////////////////////////////////////////////////////////////
      // Select between direct pass-through and registered signals

      always_comb begin
        if (state_q == TRANSPARENT) begin
          // Pass transaction signals directly to OBI
          obi_req_o   = trans_valid_i;   // Request valid
          obi_addr_o  = trans_addr_i;    // Current address
          obi_we_o    = trans_we_i;      // Current write enable
          obi_be_o    = trans_be_i;      // Current byte enable
          obi_wdata_o = trans_wdata_i;   // Current write data
          obi_atop_o  = trans_atop_i;    // Current atomic op
        end else begin
          // state_q == REGISTERED
          // Drive OBI from captured registers (stable until grant)
          obi_req_o   = 1'b1;           // Never retract request once issued
          obi_addr_o  = obi_addr_q;     // Captured address
          obi_we_o    = obi_we_q;       // Captured write enable
          obi_be_o    = obi_be_q;       // Captured byte enable
          obi_wdata_o = obi_wdata_q;    // Captured write data
          obi_atop_o  = obi_atop_q;     // Captured atomic op
        end
      end

      ///////////////////////////////////////////////////////////////////////////
      // State and Data Registers
      ///////////////////////////////////////////////////////////////////////////
      // Capture transaction on TRANSPARENT→REGISTERED transition

      //////////////////////////////////////////////////////////////////////////////
      // Registers
      //////////////////////////////////////////////////////////////////////////////

      always_ff @(posedge clk, negedge rst_n) begin
        if (rst_n == 1'b0) begin
          // Reset: Start in TRANSPARENT state, clear registers
          state_q     <= TRANSPARENT;
          obi_addr_q  <= 32'b0;
          obi_we_q    <= 1'b0;
          obi_be_q    <= 4'b0;
          obi_wdata_q <= 32'b0;
          obi_atop_q  <= 6'b0;
        end else begin
          state_q <= next_state;  // Update FSM state
          
          if ((state_q == TRANSPARENT) && (next_state == REGISTERED)) begin
            // Transitioning to REGISTERED: Capture current OBI outputs
            // Keep OBI A channel signals stable throughout REGISTERED state
            // Capture from obi_*_o (not trans_*_i) to get exact values sent to bus
            obi_addr_q  <= obi_addr_o;
            obi_we_q    <= obi_we_o;
            obi_be_q    <= obi_be_o;
            obi_wdata_q <= obi_wdata_o;
            obi_atop_q  <= obi_atop_o;
          end
          // else: Hold register values (including during REGISTERED state)
        end
      end

      ///////////////////////////////////////////////////////////////////////////
      // Transaction Ready Generation
      ///////////////////////////////////////////////////////////////////////////
      // Can accept new transaction when in TRANSPARENT state
      // In REGISTERED state, busy holding previous transaction

      // Always ready to accept a new transfer requests when previous A channel
      // transfer has been granted. Note that cv32e40p_obi_interface does not limit
      // the number of outstanding transactions in any way.
      assign trans_ready_o = (state_q == TRANSPARENT);

    end
  endgenerate

  ///////////////////////////////////////////////////////////////////////////////
  // Implementation Notes
  ///////////////////////////////////////////////////////////////////////////////
  // ALTERNATIVE IMPLEMENTATION: Transaction Queue
  // Could add internal FIFO to buffer multiple transactions:
  //   - Allows accepting new trans_valid_i even when previous not granted
  //   - Increases throughput for bursty request patterns
  //   - Requires: FIFO storage, transaction counter logic
  //   - Trade-off: Higher area vs improved bandwidth utilization
  //
  // ALTERNATIVE IMPLEMENTATION: Outstanding Transaction Limit
  // Add counter to limit maximum pending transactions:
  //   - Track trans_valid_i && trans_ready_o (requests)
  //   - Track resp_valid_o (responses)
  //   - Block trans_ready_o when counter hits limit
  //   - Prevents overwhelming slow slaves
  //   - Trade-off: Reduced throughput vs safer operation
  //
  // PERFORMANCE CONSIDERATION: Grant Latency
  // OBI slaves may take multiple cycles to assert gnt:
  //   - REGISTERED state holds transaction stable
  //   - Upstream blocked (trans_ready_o = 0) during hold
  //   - Fast grants (same cycle) maximize throughput
  //   - Slow slaves can cause pipeline stalls
  //
  // TIMING OPTIMIZATION: Pipeline OBI Outputs
  // For very high frequency designs:
  //   - Add output registers on obi_* signals
  //   - Breaks combinational path from trans_* to OBI
  //   - Cost: +1 cycle A channel latency
  //   - Benefit: Higher Fmax, easier timing closure
  //
  // VERIFICATION: Protocol Compliance
  // Key OBI protocol checks:
  //   - Assert: obi_req_o && !obi_gnt_i → addr/we/be/wdata stable next cycle
  //   - Assert: No maximum on outstanding transactions (no built-in limit)
  //   - Assert: Response always accepted (no resp backpressure)
  //   - Monitor: Transaction order vs response order (can differ)

endmodule  // cv32e40p_obi_interface
