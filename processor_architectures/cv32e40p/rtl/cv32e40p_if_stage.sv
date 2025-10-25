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
// Engineer:       Renzo Andri - andrire@student.ethz.ch                      //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
// Design Name:    Instruction Fetch Stage                                    //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Instruction fetch unit: Selection of the next PC, and      //
//                 buffering (sampling) of the read instruction               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Module: cv32e40p_if_stage
///////////////////////////////////////////////////////////////////////////////
//
// FUNCTION:
//   Instruction Fetch (IF) stage - first stage of the 4-stage pipeline.
//   Fetches instructions from memory and prepares them for decode.
//
// PIPELINE POSITION:
//   IF → ID → EX → WB
//   ^
//   This module
//
// RESPONSIBILITIES:
//   1. PC Management:
//      - Select next PC (sequential, branch, jump, exception, etc.)
//      - Calculate exception vector addresses
//      - Handle boot address
//
//   2. Instruction Fetch:
//      - Interface with prefetch buffer
//      - Request instructions from memory
//      - Handle fetch latency and stalls
//
//   3. Instruction Alignment:
//      - Handle compressed (16-bit) instructions (RV32C)
//      - Align fetched data to instruction boundaries
//      - Track PC across compressed/uncompressed mix
//
//   4. Compressed Decode:
//      - Decompress RV32C instructions to 32-bit
//      - Detect illegal compressed instructions
//      - Pass full 32-bit instructions to ID stage
//
//   5. Pipeline Control:
//      - Buffer instructions in IF/ID pipeline register
//      - Handle pipeline flushes
//      - Manage ready/valid handshakes
//
// COMPONENTS:
//   cv32e40p_if_stage (this module)
//   ├── cv32e40p_prefetch_buffer (instruction buffering & memory interface)
//   ├── cv32e40p_aligner (handle compressed instruction alignment)
//   └── cv32e40p_compressed_decoder (decompress RV32C to RV32I)
//
// PC SOURCES (pc_mux_i selection):
//   PC_BOOT      : Boot address (reset entry point)
//   PC_JUMP      : JAL/JALR jump (from ID stage)
//   PC_BRANCH    : Conditional branch taken (from EX stage)
//   PC_EXCEPTION : Exception/interrupt handler
//   PC_MRET      : Return from machine mode trap
//   PC_URET      : Return from user mode trap (PULP_SECURE)
//   PC_DRET      : Return from debug mode
//   PC_FENCEI    : FENCE.I instruction (force prefetch flush)
//   PC_HWLOOP    : Hardware loop jump (COREV_PULP)
//
// EXCEPTION VECTORS:
//   Non-vectored: All exceptions → base + 0x00
//   Vectored IRQ: Interrupts → base + (irq_id × 4)
//   Debug: dm_halt_addr_i or dm_exception_addr_i
//
// PERFORMANCE:
//   - Prefetch buffer hides memory latency
//   - Aligner handles compressed instructions with minimal stalls
//   - IF/ID register decouples fetch from decode timing
//   - Typical: 1 instruction/cycle (sequential code)
//
// TIMING:
//   - PC selected combinationally (pc_mux_i)
//   - Branch request sent to prefetch buffer (1 cycle)
//   - Instruction arrives from prefetch buffer (variable latency)
//   - Aligned and decompressed combinationally
//   - Registered in IF/ID pipeline on clock edge
//
///////////////////////////////////////////////////////////////////////////////

module cv32e40p_if_stage #(
    // PULP ISA Extension (hardware loops, custom instructions)
    // 0: Standard RV32IMC only
    // 1: Add PULP extensions (hwloop, custom CSRs, post-increment loads)
    parameter COREV_PULP = 0,
    
    // Legacy PULP OBI behavior vs. standard OBI 1.2
    // Passed to prefetch buffer
    parameter PULP_OBI = 0,
    
    // User mode and PMP support
    // 0: Machine mode only
    // 1: Machine + User modes, PMP (not fully implemented)
    parameter PULP_SECURE = 0,
    
    // Floating-point unit enable
    // Affects compressed decoder (C.FLW/C.FSW instructions)
    parameter FPU = 0,
    
    // Float in integer registers (RISC-V Zfinx extension)
    // Alternative to separate FP register file
    parameter ZFINX = 0
) (
    // ===== Clock and Reset =====
    input logic clk,
    input logic rst_n,

    // ===== Exception Vector Configuration =====
    // m_trap_base_addr_i: Machine mode trap base address
    //   - Bits [31:8] of mtvec CSR
    //   - Base for exception/interrupt vectors
    input logic [23:0] m_trap_base_addr_i,
    
    // u_trap_base_addr_i: User mode trap base address
    //   - Bits [31:8] of utvec CSR (PULP_SECURE only)
    input logic [23:0] u_trap_base_addr_i,
    
    // trap_addr_mux_i: Select machine vs. user trap vector
    //   - TRAP_MACHINE or TRAP_USER
    //   - Determines which base address to use
    input logic [ 1:0] trap_addr_mux_i,

    // ===== Boot and Debug Addresses =====
    // boot_addr_i: Reset entry point
    //   - First PC after reset
    //   - Typically ROM or flash start address
    input logic [31:0] boot_addr_i,
    
    // dm_exception_addr_i: Debug module exception handler
    //   - PC when exception occurs during debug
    input logic [31:0] dm_exception_addr_i,

    // dm_halt_addr_i: Debug mode halt address
    //   - PC when entering debug mode
    //   - Debug ROM entry point
    input logic [31:0] dm_halt_addr_i,

    // ===== Fetch Control =====
    // req_i: Enable instruction fetching
    //   - High: Normal operation, fetch instructions
    //   - Low: Stall (clock gating, sleep, debug)
    input logic req_i,

    // ===== Instruction Memory Interface (OBI) =====
    // instr_req_o: Request instruction from memory
    //   - Driven by prefetch buffer
    output logic instr_req_o,
    
    // instr_addr_o: Fetch address
    //   - Word-aligned (bits [1:0] = 2'b00)
    output logic [31:0] instr_addr_o,
    
    // instr_gnt_i: Memory grants request
    //   - Handshake with instr_req_o
    input logic instr_gnt_i,
    
    // instr_rvalid_i: Instruction data valid
    //   - Response phase of OBI transaction
    input logic instr_rvalid_i,
    
    // instr_rdata_i: Instruction data from memory
    //   - Valid when instr_rvalid_i high
    input logic [31:0] instr_rdata_i,
    
    // instr_err_i: External bus error
    //   - Validity defined by instr_rvalid_i
    //   - Not yet used (future: instruction access fault)
    input logic instr_err_i,
    
    // instr_err_pmp_i: PMP violation
    //   - Validity defined by instr_gnt_i
    //   - Not yet used (PMP not fully implemented)
    input logic instr_err_pmp_i,

    // ===== IF/ID Pipeline Output =====
    // instr_valid_id_o: Valid instruction in IF/ID register
    //   - ID stage can decode instr_rdata_id_o
    output logic instr_valid_id_o,
    
    // instr_rdata_id_o: Instruction to decode
    //   - Decompressed to 32-bit (if originally compressed)
    //   - Aligned and ready for decode
    output logic [31:0] instr_rdata_id_o,
    
    // is_compressed_id_o: Original instruction was compressed
    //   - Affects PC increment (+2 vs. +4)
    output logic is_compressed_id_o,
    
    // illegal_c_insn_id_o: Illegal compressed instruction
    //   - Compressed decoder detected invalid encoding
    output logic illegal_c_insn_id_o,
    
    // pc_if_o: Current PC in IF stage
    //   - Before IF/ID register
    output logic [31:0] pc_if_o,
    
    // pc_id_o: PC in ID stage
    //   - Registered version of pc_if_o
    //   - PC of instruction being decoded
    output logic [31:0] pc_id_o,
    
    // is_fetch_failed_o: Fetch resulted in exception
    //   - PMP violation, bus error, etc.
    //   - Not fully implemented
    output logic is_fetch_failed_o,

    // ===== Pipeline Control =====
    // clear_instr_valid_i: Flush IF/ID pipeline register
    //   - Invalidate instruction on branch, exception
    input logic clear_instr_valid_i,
    
    // pc_set_i: Set PC to new value (branch/jump/exception)
    //   - Causes prefetch buffer flush
    input logic pc_set_i,

    // ===== Exception Return Addresses =====
    // mepc_i: Machine exception PC (from mepc CSR)
    //   - PC to return to after M-mode trap
    input logic [31:0] mepc_i,
    
    // uepc_i: User exception PC (from uepc CSR)
    //   - PC to return to after U-mode trap (PULP_SECURE)
    input logic [31:0] uepc_i,

    // depc_i: Debug exception PC (from depc CSR)
    //   - PC to return to after debug mode
    input logic [31:0] depc_i,

    // ===== PC Mux Control =====
    // pc_mux_i: Select PC source
    //   - PC_BOOT, PC_JUMP, PC_BRANCH, PC_EXCEPTION, etc.
    //   - Controlled by controller FSM
    input logic [3:0] pc_mux_i,
    
    // exc_pc_mux_i: Select exception type
    //   - EXC_PC_EXCEPTION, EXC_PC_IRQ, EXC_PC_DBD, EXC_PC_DBE
    input logic [2:0] exc_pc_mux_i,

    // ===== Vectored Interrupt Support =====
    // m_exc_vec_pc_mux_i: Machine mode interrupt vector ID
    //   - Selects offset for vectored interrupts
    input  logic [4:0] m_exc_vec_pc_mux_i,
    
    // u_exc_vec_pc_mux_i: User mode interrupt vector ID
    //   - Selects offset for vectored interrupts (PULP_SECURE)
    input  logic [4:0] u_exc_vec_pc_mux_i,
    
    // csr_mtvec_init_o: Initialize mtvec on boot
    //   - Tell CSR file to set mtvec to boot address
    output logic       csr_mtvec_init_o,

    // ===== Jump/Branch Targets =====
    // jump_target_id_i: Jump target from ID stage
    //   - JAL, JALR calculated address
    input logic [31:0] jump_target_id_i,
    
    // jump_target_ex_i: Branch target from EX stage
    //   - Conditional branch address (when taken)
    input logic [31:0] jump_target_ex_i,

    // ===== Hardware Loop Control (COREV_PULP) =====
    // hwlp_jump_i: Hardware loop jump taken
    //   - Loop back to start address
    input logic        hwlp_jump_i,
    
    // hwlp_target_i: Hardware loop start address
    //   - Loop body entry point
    input logic [31:0] hwlp_target_i,

    // ===== Pipeline Stall Control =====
    // halt_if_i: Halt IF stage
    //   - From controller (debug, sleep, etc.)
    input logic halt_if_i,
    
    // id_ready_i: ID stage ready to accept instruction
    //   - Backpressure from decode stage
    input logic id_ready_i,

    // ===== Status Outputs =====
    // if_busy_o: IF stage busy fetching
    //   - Prefetch buffer has pending transactions
    output logic if_busy_o,
    
    // perf_imiss_o: Instruction fetch miss
    //   - Performance counter: fetch stall cycle
    output logic perf_imiss_o
);

  import cv32e40p_pkg::*;

  ///////////////////////////////////////////////////////////////////////////////
  // INTERNAL SIGNALS
  ///////////////////////////////////////////////////////////////////////////////
  
  // Pipeline control
  logic if_valid, if_ready;

  // Prefetch buffer interface
  logic        prefetch_busy;   // Prefetch buffer has pending transactions
  logic        branch_req;      // Request to branch (flush prefetch buffer)
  logic [31:0] branch_addr_n;   // Target address for branch

  logic        fetch_valid;     // Valid instruction from prefetch buffer
  logic        fetch_ready;     // IF stage ready to consume
  logic [31:0] fetch_rdata;     // Instruction data from prefetch buffer

  // Exception PC calculation
  logic [31:0] exc_pc;          // Calculated exception vector address

  // Vectored interrupt calculation
  logic [23:0] trap_base_addr;  // Selected trap base (M-mode or U-mode)
  logic [ 4:0] exc_vec_pc_mux;  // Selected interrupt vector ID

  // Fetch error tracking
  logic        fetch_failed;    // Fetch resulted in error (PMP/bus)

  // Aligner interface
  logic        aligner_ready;   // Aligner ready to accept new data
  logic        instr_valid;     // Aligner has valid aligned instruction

  // Compressed decoder interface
  logic        illegal_c_insn;      // Illegal compressed instruction detected
  logic [31:0] instr_aligned;       // Aligned instruction from aligner
  logic [31:0] instr_decompressed;  // Decompressed 32-bit instruction
  logic        instr_compressed_int;// Instruction was compressed


  ///////////////////////////////////////////////////////////////////////////////
  // EXCEPTION PC MUX: Calculate exception/interrupt vector address
  ///////////////////////////////////////////////////////////////////////////////
  // RISC-V privilege spec defines exception handling:
  //   - Base address from mtvec/utvec CSR
  //   - Exceptions: base + 0x00 (all go to same handler)
  //   - Interrupts: base + (cause × 4) for vectored mode
  //   - Debug: special debug module addresses
  //
  // Address calculation:
  //   Non-vectored: {trap_base_addr[23:0], 8'h0}
  //   Vectored IRQ: {trap_base_addr[23:0], 1'b0, irq_id[4:0], 2'b0}
  //   Debug halt:   dm_halt_addr_i
  //   Debug except: dm_exception_addr_i

  // exception PC selection mux
  always_comb begin : EXC_PC_MUX
    // Select M-mode or U-mode trap base address
    unique case (trap_addr_mux_i)
      TRAP_MACHINE: trap_base_addr = m_trap_base_addr_i;
      TRAP_USER:    trap_base_addr = u_trap_base_addr_i;
      default:      trap_base_addr = m_trap_base_addr_i;
    endcase

    // Select M-mode or U-mode interrupt vector ID
    unique case (trap_addr_mux_i)
      TRAP_MACHINE: exc_vec_pc_mux = m_exc_vec_pc_mux_i;
      TRAP_USER:    exc_vec_pc_mux = u_exc_vec_pc_mux_i;
      default:      exc_vec_pc_mux = m_exc_vec_pc_mux_i;
    endcase

    // Calculate final exception PC based on cause
    unique case (exc_pc_mux_i)
      // EXC_PC_EXCEPTION: All exceptions to base address
      //   RISC-V 1.10 spec: non-vectored mode
      EXC_PC_EXCEPTION:
      exc_pc = {trap_base_addr, 8'h0};
      
      // EXC_PC_IRQ: Vectored interrupts
      //   Address = base + (irq_id × 4)
      //   irq_id from exc_vec_pc_mux (0-31)
      EXC_PC_IRQ: exc_pc = {trap_base_addr, 1'b0, exc_vec_pc_mux, 2'b0};
      
      // EXC_PC_DBD: Debug mode entry
      //   Enter debug from normal execution
      EXC_PC_DBD: exc_pc = {dm_halt_addr_i[31:2], 2'b0};
      
      // EXC_PC_DBE: Debug exception
      //   Exception occurred while in debug mode
      EXC_PC_DBE: exc_pc = {dm_exception_addr_i[31:2], 2'b0};
      
      default: exc_pc = {trap_base_addr, 8'h0};
    endcase
  end

  ///////////////////////////////////////////////////////////////////////////////
  // PC MUX: Select next PC from various sources
  ///////////////////////////////////////////////////////////////////////////////
  // PC sources prioritized by controller:
  //   1. Exceptions/interrupts (highest priority)
  //   2. Debug entry/exit
  //   3. Branches/jumps
  //   4. Hardware loops
  //   5. Sequential (PC+2 or PC+4)
  //
  // Most sources provide explicit address, except sequential which is
  // handled implicitly by aligner incrementing PC.

  // fetch address selection
  always_comb begin
    // Default assign PC_BOOT (should be overwritten in below case)
    branch_addr_n = {boot_addr_i[31:2], 2'b0};

    unique case (pc_mux_i)
      // PC_BOOT: Reset entry point
      PC_BOOT: branch_addr_n = {boot_addr_i[31:2], 2'b0};
      
      // PC_JUMP: Unconditional jump (JAL, JALR)
      //   Target calculated in ID stage
      PC_JUMP: branch_addr_n = jump_target_id_i;
      
      // PC_BRANCH: Conditional branch taken
      //   Target calculated in EX stage (after condition evaluation)
      PC_BRANCH: branch_addr_n = jump_target_ex_i;
      
      // PC_EXCEPTION: Exception or interrupt handler
      //   Address from exc_pc calculation above
      PC_EXCEPTION: branch_addr_n = exc_pc;
      
      // PC_MRET: Machine mode trap return
      //   Restore PC from mepc CSR
      PC_MRET: branch_addr_n = mepc_i;
      
      // PC_URET: User mode trap return (PULP_SECURE)
      //   Restore PC from uepc CSR
      PC_URET: branch_addr_n = uepc_i;
      
      // PC_DRET: Debug mode return
      //   Restore PC from depc CSR
      PC_DRET: branch_addr_n = depc_i;
      
      // PC_FENCEI: FENCE.I instruction
      //   Forces prefetch buffer reload
      //   Jump to PC+4 (next instruction after FENCE.I)
      PC_FENCEI: branch_addr_n = pc_id_o + 4;
      
      // PC_HWLOOP: Hardware loop jump (COREV_PULP)
      //   Jump to loop start address
      PC_HWLOOP: branch_addr_n = hwlp_target_i;
      
      default: ;
    endcase
  end

  // Tell CSR register file to initialize mtvec on boot
  // mtvec initialization happens once at reset
  assign csr_mtvec_init_o = (pc_mux_i == PC_BOOT) & pc_set_i;

  // Fetch failed flag
  // PMP is not supported in CV32E40P, so always 0
  // Future: would be set on PMP violation or bus error
  assign fetch_failed    = 1'b0;

  ///////////////////////////////////////////////////////////////////////////////
  // PREFETCH BUFFER INSTANTIATION
  ///////////////////////////////////////////////////////////////////////////////
  // Decouples instruction fetch from IF stage timing.
  // Buffers instructions, hides memory latency, handles branches.

  // prefetch buffer, caches a fixed number of instructions
  cv32e40p_prefetch_buffer #(
      .PULP_OBI  (PULP_OBI),
      .COREV_PULP(COREV_PULP)
  ) prefetch_buffer_i (
      // Clock and reset
      .clk  (clk),
      .rst_n(rst_n),

      // Fetch enable
      .req_i(req_i),

      // Branch/jump control
      .branch_i     (branch_req),                        // Flush and redirect
      .branch_addr_i({branch_addr_n[31:1], 1'b0}),       // Target (halfword-aligned)

      // Hardware loop control
      .hwlp_jump_i  (hwlp_jump_i),                       // HW loop jump
      .hwlp_target_i(hwlp_target_i),                     // Loop start address

      // Handshake with IF stage
      .fetch_ready_i(fetch_ready),                       // IF ready to consume
      .fetch_valid_o(fetch_valid),                       // Valid instruction available
      .fetch_rdata_o(fetch_rdata),                       // Instruction data

      // Instruction memory interface (OBI)
      .instr_req_o    (instr_req_o),                     // Request to memory
      .instr_addr_o   (instr_addr_o),                    // Fetch address
      .instr_gnt_i    (instr_gnt_i),                     // Memory grant
      .instr_rvalid_i (instr_rvalid_i),                  // Data valid
      .instr_err_i    (instr_err_i),                     // Bus error (not supported yet)
      .instr_err_pmp_i(instr_err_pmp_i),                 // PMP error (not supported yet)
      .instr_rdata_i  (instr_rdata_i),                   // Instruction data

      // Prefetch Buffer Status
      .busy_o(prefetch_busy)                             // Has pending transactions
  );

  ///////////////////////////////////////////////////////////////////////////////
  // FETCH CONTROL LOGIC
  ///////////////////////////////////////////////////////////////////////////////
  // Manages handshakes between prefetch buffer, aligner, and ID stage.
  // Generates branch requests when PC changes.

  // offset FSM state transition logic
  always_comb begin

    fetch_ready = 1'b0;
    branch_req  = 1'b0;
    
    // Take care of jumps and branches
    if (pc_set_i) begin
      // PC is being set to new value (branch/jump/exception)
      // Flush prefetch buffer and redirect
      branch_req = 1'b1;
    end else if (fetch_valid) begin
      // Prefetch buffer has valid instruction
      if (req_i && if_valid) begin
        // IF stage active and ready to pass to ID
        // Signal prefetch buffer we consumed data
        fetch_ready = aligner_ready;
      end
    end
  end

  // Status outputs
  assign if_busy_o    = prefetch_busy;
  
  // Performance counter: instruction fetch miss
  // High when waiting for instruction (not branching)
  assign perf_imiss_o = !fetch_valid && !branch_req;

  ///////////////////////////////////////////////////////////////////////////////
  // IF/ID PIPELINE REGISTER
  ///////////////////////////////////////////////////////////////////////////////
  // Buffers instruction between fetch and decode.
  // Frozen when ID stage is stalled.
  // Flushed on branches, exceptions.

  // IF-ID pipeline registers, frozen when the ID stage is stalled
  always_ff @(posedge clk, negedge rst_n) begin : IF_ID_PIPE_REGISTERS
    if (rst_n == 1'b0) begin
      // Reset: invalidate pipeline
      instr_valid_id_o    <= 1'b0;
      instr_rdata_id_o    <= '0;
      is_fetch_failed_o   <= 1'b0;
      pc_id_o             <= '0;
      is_compressed_id_o  <= 1'b0;
      illegal_c_insn_id_o <= 1'b0;
    end else begin

      if (if_valid && instr_valid) begin
        // New valid instruction from aligner
        // Register it for ID stage
        instr_valid_id_o    <= 1'b1;
        instr_rdata_id_o    <= instr_decompressed;     // Decompressed instruction
        is_compressed_id_o  <= instr_compressed_int;   // Was compressed?
        illegal_c_insn_id_o <= illegal_c_insn;         // Illegal compressed encoding?
        is_fetch_failed_o   <= 1'b0;
        pc_id_o             <= pc_if_o;                // PC of this instruction
      end else if (clear_instr_valid_i) begin
        // Pipeline flush (branch, exception)
        // Invalidate IF/ID register
        instr_valid_id_o  <= 1'b0;
        is_fetch_failed_o <= fetch_failed;
      end
    end
  end

  ///////////////////////////////////////////////////////////////////////////////
  // PIPELINE HANDSHAKE LOGIC
  ///////////////////////////////////////////////////////////////////////////////
  // if_ready: IF stage ready to accept new instruction
  //   - Requires fetch_valid (prefetch buffer has data)
  //   - AND id_ready_i (ID stage can accept)
  //
  // if_valid: IF stage outputting valid instruction
  //   - Requires if_ready (new data available)
  //   - AND !halt_if_i (not halted by controller)

  assign if_ready = fetch_valid & id_ready_i;
  assign if_valid = (~halt_if_i) & if_ready;

  ///////////////////////////////////////////////////////////////////////////////
  // ALIGNER INSTANTIATION
  ///////////////////////////////////////////////////////////////////////////////
  // Handles compressed instruction alignment and PC tracking.
  // - Extracts 16-bit or 32-bit instructions from 32-bit fetch data
  // - Manages PC across instruction boundaries
  // - Handles misaligned compressed instructions spanning two fetches

  cv32e40p_aligner aligner_i (
      .clk             (clk),
      .rst_n           (rst_n),
      
      // Input from prefetch buffer
      .fetch_valid_i   (fetch_valid),                  // Valid fetch data
      .aligner_ready_o (aligner_ready),                // Ready to accept
      .if_valid_i      (if_valid),                     // IF stage valid
      .fetch_rdata_i   (fetch_rdata),                  // 32-bit fetch data
      
      // Output to compressed decoder
      .instr_aligned_o (instr_aligned),                // Aligned instruction
      .instr_valid_o   (instr_valid),                  // Valid aligned instruction
      
      // Branch control
      .branch_addr_i   ({branch_addr_n[31:1], 1'b0}),  // Branch target
      .branch_i        (branch_req),                   // Branch taken
      
      // Hardware loop control
      .hwlp_addr_i     (hwlp_target_i),                // HW loop target
      .hwlp_update_pc_i(hwlp_jump_i),                  // HW loop jump
      
      // PC output
      .pc_o            (pc_if_o)                       // Current PC
  );

  ///////////////////////////////////////////////////////////////////////////////
  // COMPRESSED DECODER INSTANTIATION
  ///////////////////////////////////////////////////////////////////////////////
  // Decompresses RV32C instructions to full 32-bit RV32I format.
  // - 16-bit compressed → 32-bit expanded
  // - 32-bit instructions pass through unchanged
  // - Detects illegal compressed encodings

  cv32e40p_compressed_decoder #(
      .FPU  (FPU),                                     // Affects C.FLW/C.FSW
      .ZFINX(ZFINX)                                    // FP in integer regs
  ) compressed_decoder_i (
      .instr_i        (instr_aligned),                 // Input (16 or 32-bit)
      .instr_o        (instr_decompressed),            // Output (always 32-bit)
      .is_compressed_o(instr_compressed_int),          // Was compressed?
      .illegal_instr_o(illegal_c_insn)                 // Illegal compressed?
  );

  ///////////////////////////////////////////////////////////////////////////////
  // ASSERTIONS
  ///////////////////////////////////////////////////////////////////////////////

`ifdef CV32E40P_ASSERT_ON

  ///////////////////////////////////////////////////////////////////////////
  // Assertion: Hardware loop PC mux only valid with COREV_PULP
  ///////////////////////////////////////////////////////////////////////////
  // Without PULP extensions, PC_HWLOOP should never be selected.

  generate
    if (!COREV_PULP) begin : gen_no_pulp_xpulp_assertions

      // Check that PC Mux cannot select Hardware Loop address iF PULP extensions are not included
      property p_pc_mux_0;
        @(posedge clk) disable iff (!rst_n) (1'b1) |-> (pc_mux_i != PC_HWLOOP);
      endproperty

      a_pc_mux_0 :
      assert property (p_pc_mux_0);

    end
  endgenerate

  ///////////////////////////////////////////////////////////////////////////
  // Assertion: User mode return only valid with PULP_SECURE
  ///////////////////////////////////////////////////////////////////////////
  // Without user mode support, PC_URET should never be selected.

  generate
    if (!PULP_SECURE) begin : gen_no_pulp_secure_assertions

      // Check that PC Mux cannot select URET address if User Mode is not included
      property p_pc_mux_1;
        @(posedge clk) disable iff (!rst_n) (1'b1) |-> (pc_mux_i != PC_URET);
      endproperty

      a_pc_mux_1 :
      assert property (p_pc_mux_1);

    end
  endgenerate

`endif

endmodule
