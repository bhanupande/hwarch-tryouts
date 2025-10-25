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
// Engineer:       Matthias Baer - baermatt@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Top level module                                           //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Top level module of the RISC-V core.                       //
//                 added APU, FPU parameter to include the APU_dispatcher     //
//                 and the FPU                                                //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// MODULE: cv32e40p_core
///////////////////////////////////////////////////////////////////////////////
// CV32E40P RISC-V Core - Top-Level Integration
//
// OVERVIEW:
// The cv32e40p_core is the top-level integration module for the CV32E40P
// 4-stage pipelined RISC-V processor core. It implements the RV32IMC ISA
// (32-bit base integer, multiply/divide, compressed instructions) with
// optional PULP extensions and floating-point support via APU interface.
//
// PIPELINE ARCHITECTURE:
// 4-Stage Pipeline:
//   1. IF (Instruction Fetch)
//      - Prefetch buffer with instruction cache interface
//      - PC management and branch target calculation
//      - Compressed instruction alignment
//   
//   2. ID (Instruction Decode)
//      - Instruction decoding and illegal instruction detection
//      - Register file reads
//      - Immediate generation
//      - Hazard detection and forwarding control
//      - Control transfer decision
//      - CSR access control
//   
//   3. EX (Execute)
//      - ALU operations (arithmetic, logic, shifts, PULP SIMD)
//      - Multiplier/divider
//      - Branch resolution
//      - APU/FPU offload interface
//      - Data address generation
//      - Forwarding network
//   
//   4. WB (Write Back)
//      - LSU response collection
//      - Register file write
//      - CSR update
//
// KEY COMPONENTS:
// - cv32e40p_sleep_unit: Clock gating and power management
// - cv32e40p_if_stage: Instruction fetch with prefetch buffer
// - cv32e40p_id_stage: Decode, register file, controller
// - cv32e40p_ex_stage: ALU, multiplier, APU dispatcher
// - cv32e40p_load_store_unit: Data memory interface with misalignment handling
// - cv32e40p_cs_registers: Control and status registers (CSRs)
// - cv32e40p_pmp (optional): Physical memory protection
//
// EXTENSIONS:
// - PULP Extensions (COREV_PULP=1):
//   * Hardware loops (zero-overhead loops)
//   * SIMD operations (vector arithmetic)
//   * Post-increment load/store
//   * Additional ALU operations
//   * Event load (cv.elw) for cluster synchronization
//
// - PULP Cluster Interface (COREV_CLUSTER=1):
//   * Clock enable for cluster power management
//   * Event load synchronization primitives
//
// - Floating-Point (FPU=1):
//   * IEEE 754 single/double precision via APU interface
//   * Configurable pipeline latencies
//   * FP register file (if ZFINX=0) or FP in integer RF (ZFINX=1)
//
// INTERFACES:
// - OBI (Open Bus Interface) for instruction and data memory
// - APU (Auxiliary Processing Unit) for floating-point offload
// - Interrupt controller (CLINT-compatible)
// - Debug interface (RISC-V Debug Spec 0.13)
//
// PERFORMANCE FEATURES:
// - Single-cycle execution for most ALU operations
// - Branch prediction (not taken)
// - Forwarding paths to minimize pipeline stalls
// - Multiple outstanding memory transactions (configurable)
// - Hardware performance counters (configurable count)
//
// TIMING CHARACTERISTICS:
// - Target: 1 IPC (instruction per cycle) for most operations
// - Branch penalty: 2-3 cycles (depending on target calculation)
// - Load-use penalty: 1 cycle (with forwarding)
// - Multiply: 1 cycle (MUL), multi-cycle (MULH*)
// - Divide: Multi-cycle (iterative)
//
///////////////////////////////////////////////////////////////////////////////

module cv32e40p_core
  import cv32e40p_apu_core_pkg::*;
#(
    ///////////////////////////////////////////////////////////////////////////
    // Parameters
    ///////////////////////////////////////////////////////////////////////////
    
    // COREV_PULP: Enable PULP ISA extensions
    //   0: Standard RV32IMC only
    //   1: Add PULP extensions (hardware loops, SIMD, post-inc, custom ops)
    parameter COREV_PULP =  0,
    
    // COREV_CLUSTER: Enable PULP cluster interface
    //   0: Standalone core
    //   1: Add cluster features (clock enable, event load synchronization)
    parameter COREV_CLUSTER = 0,
    
    // FPU: Enable Floating-Point Unit via APU interface
    //   0: No FPU
    //   1: FPU present (IEEE 754 single/double precision)
    parameter FPU = 0,
    
    // FPU_ADDMUL_LAT: FP addition/multiplication pipeline stages
    //   0-3: Number of pipeline registers in FP ADD/MUL lanes
    parameter FPU_ADDMUL_LAT = 0,
    
    // FPU_OTHERS_LAT: FP comparison/conversion pipeline stages
    //   0-3: Number of pipeline registers in FP CMP/CVT lanes
    parameter FPU_OTHERS_LAT = 0,
    
    // ZFINX: Floating-point in integer registers
    //   0: Separate FP register file (32 FP registers)
    //   1: FP operations use integer register file (save area)
    parameter ZFINX = 0,
    
    // NUM_MHPMCOUNTERS: Number of hardware performance counters
    //   0-29: Configurable count of HPM counters (in addition to mandatory counters)
    parameter NUM_MHPMCOUNTERS = 1
) (
    // Clock and Reset
    input logic clk_i,
    input logic rst_ni,

    input logic pulp_clock_en_i,  // PULP clock enable (only used if COREV_CLUSTER = 1)
    input logic scan_cg_en_i,  // Enable all clock gates for testing

    // Core ID, Cluster ID, debug mode halt address and boot address are considered more or less static
    input logic [31:0] boot_addr_i,
    input logic [31:0] mtvec_addr_i,
    input logic [31:0] dm_halt_addr_i,
    input logic [31:0] hart_id_i,
    input logic [31:0] dm_exception_addr_i,

    // Instruction memory interface
    output logic        instr_req_o,
    input  logic        instr_gnt_i,
    input  logic        instr_rvalid_i,
    output logic [31:0] instr_addr_o,
    input  logic [31:0] instr_rdata_i,

    // Data memory interface
    output logic        data_req_o,
    input  logic        data_gnt_i,
    input  logic        data_rvalid_i,
    output logic        data_we_o,
    output logic [ 3:0] data_be_o,
    output logic [31:0] data_addr_o,
    output logic [31:0] data_wdata_o,
    input  logic [31:0] data_rdata_i,

    ///////////////////////////////////////////////////////////////////////////
    // APU/FPU Interface (CVFPU - Core-V Floating Point Unit)
    ///////////////////////////////////////////////////////////////////////////
    // Status
    output logic apu_busy_o,                      // APU busy with operation
    
    // Request phase (handshake)
    output logic                              apu_req_o,    // APU request
    input  logic                              apu_gnt_i,    // APU grant
    
    // Request channel (operation and operands)
    output logic [   APU_NARGS_CPU-1:0][31:0] apu_operands_o,  // FP operands
    output logic [     APU_WOP_CPU-1:0]       apu_op_o,        // FP operation
    output logic [APU_NDSFLAGS_CPU-1:0]       apu_flags_o,     // FP flags (DS)
    
    // Response channel (result)
    input logic                              apu_rvalid_i,  // APU result valid
    input logic [                31:0]       apu_result_i,  // FP result
    input logic [APU_NUSFLAGS_CPU-1:0]       apu_flags_i,   // FP flags (US)

    ///////////////////////////////////////////////////////////////////////////
    // Interrupt Interface
    ///////////////////////////////////////////////////////////////////////////
    input  logic [31:0] irq_i,                    // Interrupt requests (32 sources)
    output logic        irq_ack_o,                // Interrupt acknowledge
    output logic [ 4:0] irq_id_o,                 // Acknowledged interrupt ID

    ///////////////////////////////////////////////////////////////////////////
    // Debug Interface (RISC-V Debug Spec 0.13)
    ///////////////////////////////////////////////////////////////////////////
    input  logic debug_req_i,                     // Debug request (halt)
    output logic debug_havereset_o,               // Core has been reset
    output logic debug_running_o,                 // Core is running
    output logic debug_halted_o,                  // Core is halted in debug mode

    ///////////////////////////////////////////////////////////////////////////
    // Core Control
    ///////////////////////////////////////////////////////////////////////////
    input  logic fetch_enable_i,                  // Enable instruction fetch
    output logic core_sleep_o                     // Core in sleep mode (clock gated)
);

  import cv32e40p_pkg::*;

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Parameters
  ///////////////////////////////////////////////////////////////////////////////
  // Unused parameters (left in code for future design extensions)
  localparam PULP_SECURE = 0;                     // Secure mode (not used)
  localparam N_PMP_ENTRIES = 16;                  // PMP entry count (not used)
  localparam USE_PMP = 0;                         // Physical Memory Protection (not used)
  localparam A_EXTENSION = 0;                     // Atomic extension (not used)
  localparam DEBUG_TRIGGER_EN = 1;                // Debug triggers enabled

  // PULP_OBI: OBI protocol behavior
  //   0: Standard OBI (no combinatorial paths, better timing)
  //   1: Legacy PULP OBI (allows non-stable address phase, timing critical)
  localparam PULP_OBI = 0;

  // Derived parameters
  localparam N_HWLP = 2;                          // Number of hardware loops
  localparam APU = (FPU == 1) ? 1 : 0;            // APU present if FPU enabled

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Signals - Unused
  ///////////////////////////////////////////////////////////////////////////////
  // Left in code (with their original _i, _o postfixes) for future extensions
  logic [5:0] data_atop_o;                        // Atomic operation (A_EXTENSION)
  logic       irq_sec_i;                          // Secure IRQ (PULP_SECURE)
  logic       sec_lvl_o;                          // Security level (PULP_SECURE)

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Signals - IF/ID Pipeline Interface
  ///////////////////////////////////////////////////////////////////////////////
  logic        instr_valid_id;                    // Instruction valid in ID stage
  logic [31:0] instr_rdata_id;                    // Instruction data sampled in IF
  logic        is_compressed_id;                  // Compressed instruction (16-bit)
  logic        illegal_c_insn_id;                 // Illegal compressed instruction
  logic        is_fetch_failed_id;                // Instruction fetch failed

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Signals - PC Management
  ///////////////////////////////////////////////////////////////////////////////
  logic        clear_instr_valid;                 // Clear instruction valid (flush)
  logic        pc_set;                            // PC is being updated

  logic [ 3:0] pc_mux_id;                         // PC mux selector (branch, jump, exception, etc.)
  logic [ 2:0] exc_pc_mux_id;                     // Exception PC mux selector
  logic [ 4:0] m_exc_vec_pc_mux_id;               // M-mode vectored IRQ PC selector
  logic [ 4:0] u_exc_vec_pc_mux_id;               // U-mode vectored IRQ PC selector (unused)
  logic [ 4:0] exc_cause;                         // Exception cause code

  logic [ 1:0] trap_addr_mux;                     // Trap address mux selector

  logic [31:0] pc_if;                             // Program counter in IF stage
  logic [31:0] pc_id;                             // Program counter in ID stage
  logic [31:0] pc_ex;                             // Program counter in EX stage

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Signals - Pipeline Control
  ///////////////////////////////////////////////////////////////////////////////
  logic        is_decoding;                       // ID stage is decoding instruction

  logic        useincr_addr_ex;                   // Use post-increment addressing (PULP)
  logic        data_misaligned;                   // Data access is misaligned

  logic        mult_multicycle;                   // Multiplier multi-cycle operation

  // Jump and branch control
  logic [31:0] jump_target_id;                    // Jump target from ID stage
  logic [31:0] jump_target_ex;                    // Jump target from EX stage
  logic        branch_in_ex;                      // Branch instruction in EX
  logic        branch_decision;                   // Branch taken/not taken
  logic [ 1:0] ctrl_transfer_insn_in_dec;         // Control transfer in decode

  // Pipeline busy signals
  logic        ctrl_busy;                         // Controller busy
  logic        if_busy;                           // IF stage busy
  logic        lsu_busy;                          // LSU busy

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Signals - ALU Control (ID → EX)
  ///////////////////////////////////////////////////////////////////////////////
  logic               alu_en_ex;                  // ALU enable
  alu_opcode_e        alu_operator_ex;            // ALU operation
  logic        [31:0] alu_operand_a_ex;           // ALU operand A
  logic        [31:0] alu_operand_b_ex;           // ALU operand B
  logic        [31:0] alu_operand_c_ex;           // ALU operand C
  logic        [ 4:0] bmask_a_ex;                 // Bit mask A (PULP)
  logic        [ 4:0] bmask_b_ex;                 // Bit mask B (PULP)
  logic        [ 1:0] imm_vec_ext_ex;             // Immediate vector extension (PULP)
  logic        [ 1:0] alu_vec_mode_ex;            // Vector mode (PULP SIMD)
  logic               alu_is_clpx_ex;             // Complex operation (PULP)
  logic               alu_is_subrot_ex;           // Sub-rotate operation (PULP)
  logic        [ 1:0] alu_clpx_shift_ex;          // Complex shift amount (PULP)

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Signals - Multiplier Control (ID → EX)
  ///////////////////////////////////////////////////////////////////////////////
  mul_opcode_e        mult_operator_ex;           // Multiplier operation
  logic        [31:0] mult_operand_a_ex;          // Multiplier operand A
  logic        [31:0] mult_operand_b_ex;          // Multiplier operand B
  logic        [31:0] mult_operand_c_ex;          // Multiplier operand C (accumulate)
  logic               mult_en_ex;                 // Multiplier enable
  logic               mult_sel_subword_ex;        // Subword select (16x16)
  logic        [ 1:0] mult_signed_mode_ex;        // Signed mode control
  logic        [ 4:0] mult_imm_ex;                // Immediate value
  logic        [31:0] mult_dot_op_a_ex;           // Dot product operand A (PULP)
  logic        [31:0] mult_dot_op_b_ex;           // Dot product operand B (PULP)
  logic        [31:0] mult_dot_op_c_ex;           // Dot product operand C (PULP)
  logic        [ 1:0] mult_dot_signed_ex;         // Dot product signed mode (PULP)
  logic               mult_is_clpx_ex;            // Complex multiply (PULP)
  logic        [ 1:0] mult_clpx_shift_ex;         // Complex shift (PULP)
  logic               mult_clpx_img_ex;           // Complex imaginary (PULP)

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Signals - FPU Control
  ///////////////////////////////////////////////////////////////////////////////
  logic                     fs_off;               // FPU disabled (mstatus.FS = 0)
  logic [       C_RM-1:0]   frm_csr;              // FP rounding mode (frm CSR)
  logic [    C_FFLAG-1:0]   fflags_csr;           // FP flags (fflags CSR)
  logic                     fflags_we;            // FP flags write enable
  logic                     fregs_we;             // FP register write enable

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Signals - APU Control (ID → EX)
  ///////////////////////////////////////////////////////////////////////////////
  logic                                     apu_en_ex;         // APU operation enable
  logic        [APU_NDSFLAGS_CPU-1:0]       apu_flags_ex;      // APU flags (downstream)
  logic        [     APU_WOP_CPU-1:0]       apu_op_ex;         // APU operation
  logic        [                 1:0]       apu_lat_ex;        // APU latency
  logic        [   APU_NARGS_CPU-1:0][31:0] apu_operands_ex;   // APU operands
  logic        [                 5:0]       apu_waddr_ex;      // APU destination register

  // APU dependency tracking
  logic        [                 2:0][ 5:0] apu_read_regs;         // Read register addresses
  logic        [                 2:0]       apu_read_regs_valid;   // Read register valid flags
  logic                                     apu_read_dep;          // Read dependency detected
  logic                                     apu_read_dep_for_jalr; // Read dependency for JALR
  logic        [                 1:0][ 5:0] apu_write_regs;        // Write register addresses
  logic        [                 1:0]       apu_write_regs_valid;  // Write register valid flags
  logic                                     apu_write_dep;         // Write dependency detected

  // APU performance counters
  logic                                     perf_apu_type;         // APU type conflict
  logic                                     perf_apu_cont;         // APU contention
  logic                                     perf_apu_dep;          // APU dependency stall
  logic                                     perf_apu_wb;           // APU writeback conflict

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Signals - Register File Control
  ///////////////////////////////////////////////////////////////////////////////
  // Register file write (WB stage)
  logic        [                 5:0]       regfile_waddr_ex;      // Write address (ID→EX)
  logic                                     regfile_we_ex;         // Write enable (ID→EX)
  logic        [                 5:0]       regfile_waddr_fw_wb_o; // Write address (EX→WB)
  logic                                     regfile_we_wb;         // Write enable (WB)
  logic                                     regfile_we_wb_power;   // Write enable power-qualified
  logic        [                31:0]       regfile_wdata;         // Write data (WB)

  // ALU port forwarding
  logic        [                 5:0]       regfile_alu_waddr_ex;     // ALU write address (ID→EX)
  logic                                     regfile_alu_we_ex;        // ALU write enable (ID→EX)
  logic        [                 5:0]       regfile_alu_waddr_fw;     // ALU write address forwarded
  logic                                     regfile_alu_we_fw;        // ALU write enable forwarded
  logic                                     regfile_alu_we_fw_power;  // ALU write enable power-qual
  logic        [                31:0]       regfile_alu_wdata_fw;     // ALU write data forwarded

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Signals - CSR Control
  ///////////////////////////////////////////////////////////////////////////////
  logic                                     csr_access_ex;         // CSR access in EX
  csr_opcode_e                              csr_op_ex;             // CSR operation (ID→EX)
  
  // Trap vector base addresses
  logic [23:0] mtvec;                       // M-mode trap vector base
  logic [23:0] utvec;                       // U-mode trap vector base (unused)
  logic [ 1:0] mtvec_mode;                  // M-mode vector mode
  logic [ 1:0] utvec_mode;                  // U-mode vector mode (unused)

  // CSR access interface
  csr_opcode_e        csr_op;               // CSR operation
  csr_num_e           csr_addr;             // CSR address
  csr_num_e           csr_addr_int;         // CSR address internal
  logic        [31:0] csr_rdata;            // CSR read data
  logic        [31:0] csr_wdata;            // CSR write data
  PrivLvl_t           current_priv_lvl;     // Current privilege level

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Signals - LSU Control (ID → EX → LSU)
  ///////////////////////////////////////////////////////////////////////////////
  logic               data_we_ex;           // Data write enable
  logic        [ 5:0] data_atop_ex;         // Atomic operation
  logic        [ 1:0] data_type_ex;         // Data type (word/half/byte)
  logic        [ 1:0] data_sign_ext_ex;     // Sign extension mode
  logic        [ 1:0] data_reg_offset_ex;   // Register offset
  logic               data_req_ex;          // Data request
  logic               data_load_event_ex;   // Load event (cv.elw, PULP)
  logic               data_misaligned_ex;   // Misaligned access

  // Event load signals (PULP cluster synchronization)
  logic               p_elw_start;          // cv.elw start (req sent)
  logic               p_elw_finish;         // cv.elw finish (resp received)

  // LSU read data
  logic        [31:0] lsu_rdata;            // Load data from LSU

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Signals - Pipeline Control
  ///////////////////////////////////////////////////////////////////////////////
  // Stall control
  logic               halt_if;              // Halt IF stage
  logic               id_ready;             // ID stage ready
  logic               ex_ready;             // EX stage ready

  // Valid signals
  logic               id_valid;             // ID stage valid
  logic               ex_valid;             // EX stage valid
  logic               wb_valid;             // WB stage valid

  // LSU ready signals
  logic               lsu_ready_ex;         // LSU ready in EX
  logic               lsu_ready_wb;         // LSU ready in WB

  // APU ready signal
  logic               apu_ready_wb;         // APU ready for WB

  // Instruction request
  logic               instr_req_int;        // Internal instruction request

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Signals - Interrupt and Exception Handling
  ///////////////////////////////////////////////////////////////////////////////
  logic m_irq_enable;                       // M-mode IRQ enable (mstatus.MIE)
  logic u_irq_enable;                       // U-mode IRQ enable (mstatus.UIE)
  logic csr_irq_sec;                        // Secure IRQ (unused)
  
  // Exception PC registers
  logic [31:0] mepc;                        // M-mode exception PC
  logic [31:0] uepc;                        // U-mode exception PC (unused)
  logic [31:0] depc;                        // Debug mode exception PC

  // Interrupt enable and pending
  logic [31:0] mie_bypass;                  // MIE CSR bypass
  logic [31:0] mip;                         // MIP CSR (interrupt pending)

  // Exception/interrupt save and restore
  logic        csr_save_cause;              // Save exception cause
  logic        csr_save_if;                 // Save PC from IF
  logic        csr_save_id;                 // Save PC from ID
  logic        csr_save_ex;                 // Save PC from EX
  logic [ 5:0] csr_cause;                   // Exception cause
  logic        csr_restore_mret_id;         // Restore from M-mode (MRET)
  logic        csr_restore_uret_id;         // Restore from U-mode (URET, unused)
  logic        csr_restore_dret_id;         // Restore from Debug mode (DRET)
  logic        csr_mtvec_init;              // Initialize MTVEC

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Signals - Hardware Performance Monitoring
  ///////////////////////////////////////////////////////////////////////////////
  logic [31:0] mcounteren;                  // Counter enable register

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Signals - Debug Mode
  ///////////////////////////////////////////////////////////////////////////////
  logic        debug_mode;                  // Core in debug mode
  logic [ 2:0] debug_cause;                 // Debug entry cause
  logic        debug_csr_save;              // Save CSR state
  logic        debug_single_step;           // Single-step mode enabled
  logic        debug_ebreakm;               // EBREAK in M-mode enters debug
  logic        debug_ebreaku;               // EBREAK in U-mode enters debug
  logic        trigger_match;               // Debug trigger matched
  logic        debug_p_elw_no_sleep;        // Prevent sleep during event load

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Signals - Hardware Loops (PULP)
  ///////////////////////////////////////////////////////////////////////////////
  logic [N_HWLP-1:0][31:0] hwlp_start;      // Loop start addresses
  logic [N_HWLP-1:0][31:0] hwlp_end;        // Loop end addresses
  logic [N_HWLP-1:0][31:0] hwlp_cnt;        // Loop counters

  logic [31:0] hwlp_target;                 // Hardware loop jump target
  logic        hwlp_jump;                   // Hardware loop jump active

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Signals - Performance Counter Events
  ///////////////////////////////////////////////////////////////////////////////
  logic        mhpmevent_minstret;          // Instruction retired
  logic        mhpmevent_load;              // Load instruction
  logic        mhpmevent_store;             // Store instruction
  logic        mhpmevent_jump;              // Jump instruction
  logic        mhpmevent_branch;            // Branch instruction
  logic        mhpmevent_branch_taken;      // Branch taken
  logic        mhpmevent_compressed;        // Compressed instruction
  logic        mhpmevent_jr_stall;          // Jump register stall
  logic        mhpmevent_imiss;             // Instruction cache miss
  logic        mhpmevent_ld_stall;          // Load use stall
  logic        mhpmevent_pipe_stall;        // Pipeline stall

  logic        perf_imiss;                  // Instruction miss (from IF)

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Signals - Power Management
  ///////////////////////////////////////////////////////////////////////////////
  logic        wake_from_sleep;             // Wake from sleep request

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Signals - PMP (Physical Memory Protection)
  ///////////////////////////////////////////////////////////////////////////////
  logic [N_PMP_ENTRIES-1:0][31:0] pmp_addr; // PMP address registers
  logic [N_PMP_ENTRIES-1:0][ 7:0] pmp_cfg;  // PMP configuration registers

  // PMP-gated memory interfaces
  logic        data_req_pmp;                // Data request (post-PMP)
  logic [31:0] data_addr_pmp;               // Data address (post-PMP)
  logic        data_gnt_pmp;                // Data grant (post-PMP)
  logic        data_err_pmp;                // Data access PMP error
  logic        data_err_ack;                // Data error acknowledge
  logic        instr_req_pmp;               // Instruction request (post-PMP)
  logic        instr_gnt_pmp;               // Instruction grant (post-PMP)
  logic [31:0] instr_addr_pmp;              // Instruction address (post-PMP)
  logic        instr_err_pmp;               // Instruction fetch PMP error

  ///////////////////////////////////////////////////////////////////////////////
  // Simple Wire Assignments
  ///////////////////////////////////////////////////////////////////////////////
  
  // Vectored interrupt PC calculation
  // If mtvec_mode == 0 (direct), use base address only (selector = 0)
  // If mtvec_mode == 1 (vectored), add exc_cause to base address
  assign m_exc_vec_pc_mux_id = (mtvec_mode == 2'b0) ? 5'h0 : exc_cause;
  assign u_exc_vec_pc_mux_id = (utvec_mode == 2'b0) ? 5'h0 : exc_cause;

  // Secure IRQ (unused, PULP_SECURE = 0)
  assign irq_sec_i = 1'b0;

  // APU flags pass-through to output
  assign apu_flags_o = apu_flags_ex;

  //////////////////////////////////////////////////////////////////////////////////////////////
  //   ____ _            _      __  __                                                   _    //
  //  / ___| | ___   ___| | __ |  \/  | __ _ _ __   __ _  __ _  ___ _ __ ___   ___ _ __ | |_  //
  // | |   | |/ _ \ / __| |/ / | |\/| |/ _` | '_ \ / _` |/ _` |/ _ \ '_ ` _ \ / _ \ '_ \| __| //
  // | |___| | (_) | (__|   <  | |  | | (_| | | | | (_| | (_| |  __/ | | | | |  __/ | | | |_  //
  //  \____|_|\___/ \___|_|\_\ |_|  |_|\__,_|_| |_|\__,_|\__, |\___|_| |_| |_|\___|_| |_|\__| //
  //                                                     |___/                                //
  //////////////////////////////////////////////////////////////////////////////////////////////

  ///////////////////////////////////////////////////////////////////////////////
  // CLOCK MANAGEMENT AND POWER CONTROL
  ///////////////////////////////////////////////////////////////////////////////
  // Sleep unit provides clock gating and fetch enable control
  // Manages core sleep state and wake-up from interrupts/debug
  
  logic clk;                                // Gated clock (output from sleep unit)
  logic fetch_enable;                       // Delayed fetch enable

  cv32e40p_sleep_unit #(
      .COREV_CLUSTER(COREV_CLUSTER)
  ) sleep_unit_i (
      // Clock, reset interface
      .clk_ungated_i(clk_i),                // Ungated system clock input
      .rst_n        (rst_ni),               // Reset
      .clk_gated_o  (clk),                  // Gated clock output (to all pipeline stages)
      .scan_cg_en_i (scan_cg_en_i),         // Scan clock gate enable (DFT)

      // Core sleep
      .core_sleep_o(core_sleep_o),          // Core sleep status output

      // Fetch enable
      .fetch_enable_i(fetch_enable_i),      // External fetch enable input
      .fetch_enable_o(fetch_enable),        // Delayed fetch enable (synchronized)

      // Core status (busy indicators prevent sleep)
      .if_busy_i  (if_busy),                // IF stage busy
      .ctrl_busy_i(ctrl_busy),              // Controller busy
      .lsu_busy_i (lsu_busy),               // LSU busy
      .apu_busy_i (apu_busy_o),             // APU busy

      // PULP cluster interface
      .pulp_clock_en_i       (pulp_clock_en_i),         // Cluster clock enable
      .p_elw_start_i         (p_elw_start),             // Event load start
      .p_elw_finish_i        (p_elw_finish),            // Event load finish
      .debug_p_elw_no_sleep_i(debug_p_elw_no_sleep),    // Prevent sleep during debug event load

      // WFI wake
      .wake_from_sleep_i(wake_from_sleep)   // Wake from sleep (IRQ/debug)
  );


  //////////////////////////////////////////////////
  //   ___ _____   ____ _____  _    ____ _____    //
  //  |_ _|  ___| / ___|_   _|/ \  / ___| ____|   //
  //   | || |_    \___ \ | | / _ \| |  _|  _|     //
  //   | ||  _|    ___) || |/ ___ \ |_| | |___    //
  //  |___|_|     |____/ |_/_/   \_\____|_____|   //
  //                                              //
  //////////////////////////////////////////////////

  ///////////////////////////////////////////////////////////////////////////////
  // INSTRUCTION FETCH STAGE
  ///////////////////////////////////////////////////////////////////////////////
  // Fetches instructions from memory via OBI protocol
  // Includes prefetch buffer, PC management, compressed instruction alignment
  
  cv32e40p_if_stage #(
      .COREV_PULP (COREV_PULP),
      .PULP_OBI   (PULP_OBI),
      .PULP_SECURE(PULP_SECURE),
      .FPU        (FPU),
      .ZFINX      (ZFINX)
  ) if_stage_i (
      // Clock and reset
      .clk  (clk),
      .rst_n(rst_ni),

      // Configuration addresses
      .boot_addr_i        (boot_addr_i[31:0]),          // Boot address (reset PC)
      .dm_exception_addr_i(dm_exception_addr_i[31:0]),  // Debug exception address
      .dm_halt_addr_i     (dm_halt_addr_i[31:0]),       // Debug halt address

      // Trap vector addresses
      .m_trap_base_addr_i(mtvec),                       // M-mode trap base
      .u_trap_base_addr_i(utvec),                       // U-mode trap base (unused)
      .trap_addr_mux_i   (trap_addr_mux),               // Trap address mux selector

      // Instruction request control
      .req_i(instr_req_int),                            // Request from ID stage

      // Instruction memory interface (OBI)
      .instr_req_o    (instr_req_pmp),                  // Request to PMP/memory
      .instr_addr_o   (instr_addr_pmp),                 // Address to PMP/memory
      .instr_gnt_i    (instr_gnt_pmp),                  // Grant from PMP/memory
      .instr_rvalid_i (instr_rvalid_i),                 // Response valid from memory
      .instr_rdata_i  (instr_rdata_i),                  // Instruction data from memory
      .instr_err_i    (1'b0),                           // Bus error (not used yet)
      .instr_err_pmp_i(instr_err_pmp),                  // PMP error

      // Outputs to ID stage
      .instr_valid_id_o (instr_valid_id),               // Instruction valid
      .instr_rdata_id_o (instr_rdata_id),               // Instruction data
      .is_fetch_failed_o(is_fetch_failed_id),           // Fetch failed

      // Control signals from ID
      .clear_instr_valid_i(clear_instr_valid),          // Clear/flush instruction
      .pc_set_i           (pc_set),                     // PC update request

      // Exception/debug return addresses
      .mepc_i(mepc),                                    // M-mode exception PC
      .uepc_i(uepc),                                    // U-mode exception PC (unused)
      .depc_i(depc),                                    // Debug mode exception PC

      // PC control
      .pc_mux_i    (pc_mux_id),                         // PC mux selector
      .exc_pc_mux_i(exc_pc_mux_id),                     // Exception PC mux selector

      // PC outputs
      .pc_id_o(pc_id),                                  // PC in ID stage
      .pc_if_o(pc_if),                                  // PC in IF stage

      // Compressed instruction info
      .is_compressed_id_o (is_compressed_id),           // Instruction is compressed
      .illegal_c_insn_id_o(illegal_c_insn_id),          // Illegal compressed instruction

      // Vectored interrupt PC calculation
      .m_exc_vec_pc_mux_i(m_exc_vec_pc_mux_id),        // M-mode vectored IRQ offset
      .u_exc_vec_pc_mux_i(u_exc_vec_pc_mux_id),        // U-mode vectored IRQ offset

      // MTVEC initialization
      .csr_mtvec_init_o(csr_mtvec_init),                // MTVEC init flag

      // Hardware loop control (PULP)
      .hwlp_jump_i  (hwlp_jump),                        // Hardware loop jump
      .hwlp_target_i(hwlp_target),                      // Hardware loop target

      // Jump targets from ID and EX stages
      .jump_target_id_i(jump_target_id),                // Jump target computed in ID
      .jump_target_ex_i(jump_target_ex),                // Jump target computed in EX

      // Pipeline stalls and ready signals
      .halt_if_i (halt_if),                             // Halt IF stage
      .id_ready_i(id_ready),                            // ID stage ready

      // Status outputs
      .if_busy_o   (if_busy),                           // IF stage busy
      .perf_imiss_o(perf_imiss)                         // Instruction cache miss counter
  );


  ///////////////////////////////////////////////////////////////////////////////
  // INSTRUCTION DECODE STAGE
  ///////////////////////////////////////////////////////////////////////////////
  // Decodes instructions, generates control signals, manages register file
  // Includes decoder, register file, hazard detection, forwarding control
  // Instantiates the main controller
  
  cv32e40p_id_stage #(
      .COREV_PULP      (COREV_PULP),                   // Enable PULP ISA extensions
      .COREV_CLUSTER   (COREV_CLUSTER),                // Enable cluster support
      .N_HWLP          (N_HWLP),                       // Number of hardware loops
      .PULP_SECURE     (PULP_SECURE),                  // Enable security features
      .USE_PMP         (USE_PMP),                      // Enable PMP
      .A_EXTENSION     (A_EXTENSION),                  // Enable atomic extension
      .APU             (APU),                          // Enable APU
      .FPU             (FPU),                          // Enable FPU
      .FPU_ADDMUL_LAT  (FPU_ADDMUL_LAT),              // FPU add/mul latency
      .FPU_OTHERS_LAT  (FPU_OTHERS_LAT),              // FPU other ops latency
      .ZFINX           (ZFINX),                        // FPU in integer registers
      .APU_NARGS_CPU   (APU_NARGS_CPU),               // APU operand count
      .APU_WOP_CPU     (APU_WOP_CPU),                 // APU operation width
      .APU_NDSFLAGS_CPU(APU_NDSFLAGS_CPU),            // APU dependency flags
      .APU_NUSFLAGS_CPU(APU_NUSFLAGS_CPU),            // APU use flags
      .DEBUG_TRIGGER_EN(DEBUG_TRIGGER_EN)             // Enable debug triggers
  ) id_stage_i (
      // Clock and reset
      .clk          (clk),                             // Gated clock
      .clk_ungated_i(clk_i),                          // Ungated clock for clock gating
      .rst_n        (rst_ni),

      .scan_cg_en_i(scan_cg_en_i),                    // Scan clock gate enable

      // Processor enable and status
      .fetch_enable_i(fetch_enable),                  // Delayed fetch enable
      .ctrl_busy_o   (ctrl_busy),                     // Controller busy
      .is_decoding_o (is_decoding),                   // Currently decoding

      // Interface to IF stage
      .instr_valid_i(instr_valid_id),                 // Instruction valid from IF
      .instr_rdata_i(instr_rdata_id),                 // Instruction data from IF
      .instr_req_o  (instr_req_int),                  // Instruction request to IF

      // Jumps and branches
      .branch_in_ex_o             (branch_in_ex),                 // Branch in EX
      .branch_decision_i          (branch_decision),              // Branch taken from EX
      .jump_target_o              (jump_target_id),               // Jump target to IF
      .ctrl_transfer_insn_in_dec_o(ctrl_transfer_insn_in_dec),   // Control transfer in decode

      // IF stage control
      .clear_instr_valid_o(clear_instr_valid),        // Clear IF instruction
      .pc_set_o           (pc_set),                   // Set PC request
      .pc_mux_o           (pc_mux_id),                // PC mux selector
      .exc_pc_mux_o       (exc_pc_mux_id),            // Exception PC mux
      .exc_cause_o        (exc_cause),                // Exception cause
      .trap_addr_mux_o    (trap_addr_mux),            // Trap address mux

      .is_fetch_failed_i(is_fetch_failed_id),         // Fetch failed from IF

      .pc_id_i(pc_id),                                // PC from IF

      .is_compressed_i (is_compressed_id),            // Compressed instruction
      .illegal_c_insn_i(illegal_c_insn_id),           // Illegal compressed

      // Pipeline stalls and ready signals
      .halt_if_o(halt_if),                            // Halt IF stage

      .id_ready_o(id_ready),                          // ID ready
      .ex_ready_i(ex_ready),                          // EX ready
      .wb_ready_i(lsu_ready_wb),                      // WB ready

      .id_valid_o(id_valid),                          // ID valid
      .ex_valid_i(ex_valid),                          // EX valid

      // PC to EX stage
      .pc_ex_o(pc_ex),                                // PC to EX

      // ALU control signals to EX stage
      .alu_en_ex_o        (alu_en_ex),                // ALU enable
      .alu_operator_ex_o  (alu_operator_ex),          // ALU operation
      .alu_operand_a_ex_o (alu_operand_a_ex),         // ALU operand A
      .alu_operand_b_ex_o (alu_operand_b_ex),         // ALU operand B
      .alu_operand_c_ex_o (alu_operand_c_ex),         // ALU operand C
      .bmask_a_ex_o       (bmask_a_ex),               // Bit mask A
      .bmask_b_ex_o       (bmask_b_ex),               // Bit mask B
      .imm_vec_ext_ex_o   (imm_vec_ext_ex),           // Vector immediate extension
      .alu_vec_mode_ex_o  (alu_vec_mode_ex),          // Vector mode
      .alu_is_clpx_ex_o   (alu_is_clpx_ex),           // Complex ALU operation
      .alu_is_subrot_ex_o (alu_is_subrot_ex),         // Sub-rotate operation
      .alu_clpx_shift_ex_o(alu_clpx_shift_ex),        // Complex shift

      // Register file write control
      .regfile_waddr_ex_o(regfile_waddr_ex),          // Write address
      .regfile_we_ex_o   (regfile_we_ex),             // Write enable

      .regfile_alu_we_ex_o   (regfile_alu_we_ex),     // ALU write enable
      .regfile_alu_waddr_ex_o(regfile_alu_waddr_ex),  // ALU write address

      // Multiplier control signals to EX stage
      .mult_operator_ex_o   (mult_operator_ex),       // Multiplier operation
      .mult_en_ex_o         (mult_en_ex),             // Multiplier enable
      .mult_sel_subword_ex_o(mult_sel_subword_ex),    // Subword select
      .mult_signed_mode_ex_o(mult_signed_mode_ex),    // Signed mode
      .mult_operand_a_ex_o  (mult_operand_a_ex),      // Operand A
      .mult_operand_b_ex_o  (mult_operand_b_ex),      // Operand B
      .mult_operand_c_ex_o  (mult_operand_c_ex),      // Operand C
      .mult_imm_ex_o        (mult_imm_ex),            // Immediate

      .mult_dot_op_a_ex_o  (mult_dot_op_a_ex),        // Dot product operand A
      .mult_dot_op_b_ex_o  (mult_dot_op_b_ex),        // Dot product operand B
      .mult_dot_op_c_ex_o  (mult_dot_op_c_ex),        // Dot product operand C
      .mult_dot_signed_ex_o(mult_dot_signed_ex),      // Dot product signed
      .mult_is_clpx_ex_o   (mult_is_clpx_ex),         // Complex multiply
      .mult_clpx_shift_ex_o(mult_clpx_shift_ex),      // Complex shift
      .mult_clpx_img_ex_o  (mult_clpx_img_ex),        // Complex imaginary

      // FPU inputs from CSR
      .fs_off_i(fs_off),                              // FPU disabled
      .frm_i   (frm_csr),                             // Rounding mode

      // APU control signals to EX stage
      .apu_en_ex_o      (apu_en_ex),                  // APU enable
      .apu_op_ex_o      (apu_op_ex),                  // APU operation
      .apu_lat_ex_o     (apu_lat_ex),                 // APU latency
      .apu_operands_ex_o(apu_operands_ex),            // APU operands
      .apu_flags_ex_o   (apu_flags_ex),               // APU flags
      .apu_waddr_ex_o   (apu_waddr_ex),               // APU write address

      .apu_read_regs_o        (apu_read_regs),               // APU read registers
      .apu_read_regs_valid_o  (apu_read_regs_valid),         // APU read valid
      .apu_read_dep_i         (apu_read_dep),                // APU read dependency
      .apu_read_dep_for_jalr_i(apu_read_dep_for_jalr),       // APU dependency for JALR
      .apu_write_regs_o       (apu_write_regs),              // APU write registers
      .apu_write_regs_valid_o (apu_write_regs_valid),        // APU write valid
      .apu_write_dep_i        (apu_write_dep),               // APU write dependency
      .apu_perf_dep_o         (perf_apu_dep),                // APU dependency stall
      .apu_busy_i             (apu_busy_o),                  // APU busy

      // CSR signals
      .csr_access_ex_o      (csr_access_ex),          // CSR access
      .csr_op_ex_o          (csr_op_ex),              // CSR operation
      .current_priv_lvl_i   (current_priv_lvl),       // Current privilege level
      .csr_irq_sec_o        (csr_irq_sec),            // Secure IRQ
      .csr_cause_o          (csr_cause),              // Exception/interrupt cause
      .csr_save_if_o        (csr_save_if),            // Save PC from IF
      .csr_save_id_o        (csr_save_id),            // Save PC from ID
      .csr_save_ex_o        (csr_save_ex),            // Save PC from EX
      .csr_restore_mret_id_o(csr_restore_mret_id),    // Restore from M-mode
      .csr_restore_uret_id_o(csr_restore_uret_id),    // Restore from U-mode

      .csr_restore_dret_id_o(csr_restore_dret_id),    // Restore from debug

      .csr_save_cause_o(csr_save_cause),              // Save cause

      // Hardware loop control to IF stage (PULP)
      .hwlp_start_o(hwlp_start),                      // Loop start addresses
      .hwlp_end_o  (hwlp_end),                        // Loop end addresses
      .hwlp_cnt_o  (hwlp_cnt),                        // Loop counters

      .hwlp_jump_o  (hwlp_jump),                      // Loop jump
      .hwlp_target_o(hwlp_target),                    // Loop target

      // Load/Store Unit control to EX stage
      .data_req_ex_o       (data_req_ex),             // Data request
      .data_we_ex_o        (data_we_ex),              // Data write enable
      .atop_ex_o           (data_atop_ex),            // Atomic operation
      .data_type_ex_o      (data_type_ex),            // Data type
      .data_sign_ext_ex_o  (data_sign_ext_ex),        // Sign extension
      .data_reg_offset_ex_o(data_reg_offset_ex),      // Register offset
      .data_load_event_ex_o(data_load_event_ex),      // Load event

      .data_misaligned_ex_o(data_misaligned_ex),      // Misaligned access

      .prepost_useincr_ex_o(useincr_addr_ex),         // Use increment address
      .data_misaligned_i   (data_misaligned),         // Misaligned from LSU
      .data_err_i          (data_err_pmp),            // PMP error
      .data_err_ack_o      (data_err_ack),            // Error acknowledge

      // Interrupt signals
      .irq_i         (irq_i),                         // External interrupts
      .irq_sec_i     ((PULP_SECURE) ? irq_sec_i : 1'b0),  // Secure interrupts
      .mie_bypass_i  (mie_bypass),                    // MIE bypass
      .mip_o         (mip),                           // Pending interrupts
      .m_irq_enable_i(m_irq_enable),                  // M-mode IRQ enable
      .u_irq_enable_i(u_irq_enable),                  // U-mode IRQ enable
      .irq_ack_o     (irq_ack_o),                     // IRQ acknowledge
      .irq_id_o      (irq_id_o),                      // IRQ ID

      // Debug signals
      .debug_mode_o          (debug_mode),            // Debug mode active
      .debug_cause_o         (debug_cause),           // Debug cause
      .debug_csr_save_o      (debug_csr_save),        // Save CSR for debug
      .debug_req_i           (debug_req_i),           // Debug request
      .debug_havereset_o     (debug_havereset_o),     // Have reset
      .debug_running_o       (debug_running_o),       // Running
      .debug_halted_o        (debug_halted_o),        // Halted
      .debug_single_step_i   (debug_single_step),     // Single step
      .debug_ebreakm_i       (debug_ebreakm),         // EBREAK in M-mode
      .debug_ebreaku_i       (debug_ebreaku),         // EBREAK in U-mode
      .trigger_match_i       (trigger_match),         // Trigger match
      .debug_p_elw_no_sleep_o(debug_p_elw_no_sleep),  // No sleep on p.elw

      // Wakeup signal
      .wake_from_sleep_o(wake_from_sleep),            // Wake from sleep

      // Forward signals from WB stage
      .regfile_waddr_wb_i   (regfile_waddr_fw_wb_o),  // Write address from WB
      .regfile_we_wb_i      (regfile_we_wb),          // Write enable from WB
      .regfile_we_wb_power_i(regfile_we_wb_power),    // Write enable (power)
      .regfile_wdata_wb_i   (regfile_wdata),          // Write data from WB

      .regfile_alu_waddr_fw_i   (regfile_alu_waddr_fw),      // ALU write address forward
      .regfile_alu_we_fw_i      (regfile_alu_we_fw),         // ALU write enable forward
      .regfile_alu_we_fw_power_i(regfile_alu_we_fw_power),   // ALU write enable (power)
      .regfile_alu_wdata_fw_i   (regfile_alu_wdata_fw),      // ALU write data forward

      // Multiplier multicycle feedback
      .mult_multicycle_i(mult_multicycle),            // Multiplier multicycle

      // Performance counter events
      .mhpmevent_minstret_o    (mhpmevent_minstret),      // Instruction retired
      .mhpmevent_load_o        (mhpmevent_load),          // Load instruction
      .mhpmevent_store_o       (mhpmevent_store),         // Store instruction
      .mhpmevent_jump_o        (mhpmevent_jump),          // Jump instruction
      .mhpmevent_branch_o      (mhpmevent_branch),        // Branch instruction
      .mhpmevent_branch_taken_o(mhpmevent_branch_taken),  // Branch taken
      .mhpmevent_compressed_o  (mhpmevent_compressed),    // Compressed instruction
      .mhpmevent_jr_stall_o    (mhpmevent_jr_stall),      // Jump register stall
      .mhpmevent_imiss_o       (mhpmevent_imiss),         // Instruction miss
      .mhpmevent_ld_stall_o    (mhpmevent_ld_stall),      // Load stall
      .mhpmevent_pipe_stall_o  (mhpmevent_pipe_stall),    // Pipeline stall

      .perf_imiss_i(perf_imiss),                      // Instruction miss from IF
      .mcounteren_i(mcounteren)                       // Counter enable
  );


  ///////////////////////////////////////////////////////////////////////////////
  // EXECUTE STAGE
  ///////////////////////////////////////////////////////////////////////////////
  // Performs ALU operations, multiplication, branch decision
  // Interfaces with FPU/APU for floating-point operations
  // Manages register writeback pipeline
  
  cv32e40p_ex_stage #(
      .COREV_PULP      (COREV_PULP),                   // Enable PULP ISA extensions
      .FPU             (FPU),                          // Enable FPU
      .APU_NARGS_CPU   (APU_NARGS_CPU),               // APU operand count
      .APU_WOP_CPU     (APU_WOP_CPU),                 // APU operation width
      .APU_NDSFLAGS_CPU(APU_NDSFLAGS_CPU),            // APU dependency flags
      .APU_NUSFLAGS_CPU(APU_NUSFLAGS_CPU)             // APU use flags
  ) ex_stage_i (
      // Clock and reset
      .clk  (clk),
      .rst_n(rst_ni),

      // ALU control signals from ID stage
      .alu_en_i        (alu_en_ex),                    // ALU enable
      .alu_operator_i  (alu_operator_ex),              // ALU operation
      .alu_operand_a_i (alu_operand_a_ex),             // Operand A
      .alu_operand_b_i (alu_operand_b_ex),             // Operand B
      .alu_operand_c_i (alu_operand_c_ex),             // Operand C (store data)
      .bmask_a_i       (bmask_a_ex),                   // Bit mask A
      .bmask_b_i       (bmask_b_ex),                   // Bit mask B
      .imm_vec_ext_i   (imm_vec_ext_ex),               // Vector immediate extension
      .alu_vec_mode_i  (alu_vec_mode_ex),              // Vector mode
      .alu_is_clpx_i   (alu_is_clpx_ex),               // Complex ALU operation
      .alu_is_subrot_i (alu_is_subrot_ex),             // Sub-rotate operation
      .alu_clpx_shift_i(alu_clpx_shift_ex),            // Complex shift

      // Multiplier control signals from ID stage
      .mult_operator_i   (mult_operator_ex),           // Multiplier operation
      .mult_operand_a_i  (mult_operand_a_ex),          // Operand A
      .mult_operand_b_i  (mult_operand_b_ex),          // Operand B
      .mult_operand_c_i  (mult_operand_c_ex),          // Operand C (accumulate)
      .mult_en_i         (mult_en_ex),                 // Multiplier enable
      .mult_sel_subword_i(mult_sel_subword_ex),        // Subword select
      .mult_signed_mode_i(mult_signed_mode_ex),        // Signed mode
      .mult_imm_i        (mult_imm_ex),                // Immediate
      .mult_dot_op_a_i   (mult_dot_op_a_ex),           // Dot product operand A
      .mult_dot_op_b_i   (mult_dot_op_b_ex),           // Dot product operand B
      .mult_dot_op_c_i   (mult_dot_op_c_ex),           // Dot product operand C
      .mult_dot_signed_i (mult_dot_signed_ex),         // Dot product signed
      .mult_is_clpx_i    (mult_is_clpx_ex),            // Complex multiply
      .mult_clpx_shift_i (mult_clpx_shift_ex),         // Complex shift
      .mult_clpx_img_i   (mult_clpx_img_ex),           // Complex imaginary

      .mult_multicycle_o(mult_multicycle),             // Multicycle feedback to ID

      // LSU interface
      .data_req_i          (data_req_o),               // Data request to memory
      .data_rvalid_i       (data_rvalid_i),            // Response valid from memory
      .data_misaligned_ex_i(data_misaligned_ex),       // Misaligned from ID
      .data_misaligned_i   (data_misaligned),          // Misaligned from LSU

      .ctrl_transfer_insn_in_dec_i(ctrl_transfer_insn_in_dec),  // Control transfer in decode

      // FPU flags
      .fpu_fflags_we_o(fflags_we),                     // FP flags write enable
      .fpu_fflags_o   (fflags_csr),                    // FP flags value

      // APU control from ID stage
      .apu_en_i      (apu_en_ex),                      // APU enable
      .apu_op_i      (apu_op_ex),                      // APU operation
      .apu_lat_i     (apu_lat_ex),                     // APU latency
      .apu_operands_i(apu_operands_ex),                // APU operands
      .apu_waddr_i   (apu_waddr_ex),                   // APU write address

      .apu_read_regs_i        (apu_read_regs),         // APU read registers
      .apu_read_regs_valid_i  (apu_read_regs_valid),   // APU read valid
      .apu_read_dep_o         (apu_read_dep),          // APU read dependency
      .apu_read_dep_for_jalr_o(apu_read_dep_for_jalr), // APU dependency for JALR
      .apu_write_regs_i       (apu_write_regs),        // APU write registers
      .apu_write_regs_valid_i (apu_write_regs_valid),  // APU write valid
      .apu_write_dep_o        (apu_write_dep),         // APU write dependency

      .apu_perf_type_o(perf_apu_type),                 // APU perf type
      .apu_perf_cont_o(perf_apu_cont),                 // APU perf continue
      .apu_perf_wb_o  (perf_apu_wb),                   // APU perf WB
      .apu_ready_wb_o (apu_ready_wb),                  // APU ready in WB
      .apu_busy_o     (apu_busy_o),                    // APU busy

      // APU/FPU interface (external)
      .apu_req_o     (apu_req_o),                      // Request to FPU
      .apu_gnt_i     (apu_gnt_i),                      // Grant from FPU
      .apu_operands_o(apu_operands_o),                 // Operands to FPU
      .apu_op_o      (apu_op_o),                       // Operation to FPU
      .apu_rvalid_i  (apu_rvalid_i),                   // Response valid from FPU
      .apu_result_i  (apu_result_i),                   // Result from FPU
      .apu_flags_i   (apu_flags_i),                    // Flags from FPU

      .lsu_en_i   (data_req_ex),                       // LSU enable from ID
      .lsu_rdata_i(lsu_rdata),                         // LSU read data

      // CSR interface
      .csr_access_i(csr_access_ex),                    // CSR access
      .csr_rdata_i (csr_rdata),                        // CSR read data

      // Register file control from ID
      .branch_in_ex_i     (branch_in_ex),              // Branch in EX
      .regfile_alu_waddr_i(regfile_alu_waddr_ex),      // ALU write address
      .regfile_alu_we_i   (regfile_alu_we_ex),         // ALU write enable

      .regfile_waddr_i(regfile_waddr_ex),              // Write address
      .regfile_we_i   (regfile_we_ex),                 // Write enable

      // Register writeback to WB stage
      .regfile_waddr_wb_o   (regfile_waddr_fw_wb_o),   // Write address to WB
      .regfile_we_wb_o      (regfile_we_wb),           // Write enable to WB
      .regfile_we_wb_power_o(regfile_we_wb_power),     // Write enable (power tracking)
      .regfile_wdata_wb_o   (regfile_wdata),           // Write data to WB

      // Branch decision to IF stage
      .jump_target_o    (jump_target_ex),              // Jump target
      .branch_decision_o(branch_decision),             // Branch taken/not taken

      // ALU forwarding to ID stage
      .regfile_alu_waddr_fw_o   (regfile_alu_waddr_fw),      // ALU write address forward
      .regfile_alu_we_fw_o      (regfile_alu_we_fw),         // ALU write enable forward
      .regfile_alu_we_fw_power_o(regfile_alu_we_fw_power),   // ALU write enable (power tracking)
      .regfile_alu_wdata_fw_o   (regfile_alu_wdata_fw),      // ALU write data forward

      // Stall control
      .is_decoding_i (is_decoding),                    // Decoding in ID
      .lsu_ready_ex_i(lsu_ready_ex),                   // LSU ready in EX
      .lsu_err_i     (data_err_pmp),                   // PMP error

      // Pipeline control
      .ex_ready_o(ex_ready),                           // EX ready
      .ex_valid_o(ex_valid),                           // EX valid
      .wb_ready_i(lsu_ready_wb)                        // WB ready
  );


  ///////////////////////////////////////////////////////////////////////////////
  // LOAD/STORE UNIT
  ///////////////////////////////////////////////////////////////////////////////
  // Handles data memory accesses: loads, stores, atomic operations
  // Performs address generation, alignment, sign extension
  // Manages misaligned access splitting
  
  cv32e40p_load_store_unit #(
      .PULP_OBI(PULP_OBI)                              // OBI protocol mode
  ) load_store_unit_i (
      // Clock and reset
      .clk  (clk),
      .rst_n(rst_ni),

      // Data memory interface (OBI)
      .data_req_o    (data_req_pmp),                   // Request to PMP/memory
      .data_gnt_i    (data_gnt_pmp),                   // Grant from PMP/memory
      .data_rvalid_i (data_rvalid_i),                  // Response valid from memory
      .data_err_i    (1'b0),                           // Bus error (not used yet)
      .data_err_pmp_i(data_err_pmp),                   // PMP error

      .data_addr_o (data_addr_pmp),                    // Address to PMP/memory
      .data_we_o   (data_we_o),                        // Write enable to memory
      .data_atop_o (data_atop_o),                      // Atomic operation
      .data_be_o   (data_be_o),                        // Byte enable to memory
      .data_wdata_o(data_wdata_o),                     // Write data to memory
      .data_rdata_i(data_rdata_i),                     // Read data from memory

      // Signals from EX stage
      .data_we_ex_i        (data_we_ex),               // Write enable from ID/EX
      .data_atop_ex_i      (data_atop_ex),             // Atomic operation from ID/EX
      .data_type_ex_i      (data_type_ex),             // Data type (byte/half/word)
      .data_wdata_ex_i     (alu_operand_c_ex),         // Write data from EX
      .data_reg_offset_ex_i(data_reg_offset_ex),       // Register offset
      .data_load_event_ex_i(data_load_event_ex),       // Load event request
      .data_sign_ext_ex_i  (data_sign_ext_ex),         // Sign extension enable

      .data_rdata_ex_o  (lsu_rdata),                   // Read data to EX
      .data_req_ex_i    (data_req_ex),                 // Request from ID/EX
      .operand_a_ex_i   (alu_operand_a_ex),            // Base address from EX
      .operand_b_ex_i   (alu_operand_b_ex),            // Offset from EX
      .addr_useincr_ex_i(useincr_addr_ex),             // Use increment address

      .data_misaligned_ex_i(data_misaligned_ex),       // Misaligned from ID/EX
      .data_misaligned_o   (data_misaligned),          // Misaligned to ID/EX

      // Load event signaling (PULP)
      .p_elw_start_o (p_elw_start),                    // Load event start
      .p_elw_finish_o(p_elw_finish),                   // Load event finish

      // Pipeline control
      .lsu_ready_ex_o(lsu_ready_ex),                   // LSU ready in EX
      .lsu_ready_wb_o(lsu_ready_wb),                   // LSU ready in WB

      .busy_o(lsu_busy)                                // LSU busy
  );

  // Tracer signal
  assign wb_valid = lsu_ready_wb;


  ///////////////////////////////////////////////////////////////////////////////
  // CONTROL AND STATUS REGISTERS (CSRs)
  ///////////////////////////////////////////////////////////////////////////////
  // Implements all CSRs: machine/user mode, FPU, debug, PMP, performance counters
  // Manages exceptions, interrupts, and privilege levels
  
  cv32e40p_cs_registers #(
      .N_HWLP          (N_HWLP),                       // Number of hardware loops
      .A_EXTENSION     (A_EXTENSION),                  // Atomic extension
      .FPU             (FPU),                          // Enable FPU
      .ZFINX           (ZFINX),                        // FPU in integer registers
      .APU             (APU),                          // Enable APU
      .PULP_SECURE     (PULP_SECURE),                  // Security features
      .USE_PMP         (USE_PMP),                      // Enable PMP
      .N_PMP_ENTRIES   (N_PMP_ENTRIES),                // Number of PMP entries
      .NUM_MHPMCOUNTERS(NUM_MHPMCOUNTERS),             // Number of perf counters
      .COREV_PULP      (COREV_PULP),                   // PULP extensions
      .COREV_CLUSTER   (COREV_CLUSTER),                // Cluster support
      .DEBUG_TRIGGER_EN(DEBUG_TRIGGER_EN)              // Debug triggers
  ) cs_registers_i (
      // Clock and reset
      .clk  (clk),
      .rst_n(rst_ni),

      // Configuration
      .hart_id_i       (hart_id_i),                    // Hardware thread ID
      .mtvec_o         (mtvec),                        // M-mode trap vector base
      .utvec_o         (utvec),                        // U-mode trap vector base
      .mtvec_mode_o    (mtvec_mode),                   // M-mode vector mode
      .utvec_mode_o    (utvec_mode),                   // U-mode vector mode
      .mtvec_addr_i    (mtvec_addr_i[31:0]),           // MTVEC initialization value
      .csr_mtvec_init_i(csr_mtvec_init),               // MTVEC initialization flag

      // CSR access interface (SRAM-like)
      .csr_addr_i      (csr_addr),                     // CSR address
      .csr_wdata_i     (csr_wdata),                    // CSR write data
      .csr_op_i        (csr_op),                       // CSR operation
      .csr_rdata_o     (csr_rdata),                    // CSR read data

      // FPU CSRs
      .fs_off_o   (fs_off),                            // FPU disabled
      .frm_o      (frm_csr),                           // Rounding mode
      .fflags_i   (fflags_csr),                        // FP flags from FPU
      .fflags_we_i(fflags_we),                         // FP flags write enable
      .fregs_we_i (fregs_we),                          // FP registers write enable

      // Interrupt control
      .mie_bypass_o  (mie_bypass),                     // MIE bypass
      .mip_i         (mip),                            // Pending interrupts
      .m_irq_enable_o(m_irq_enable),                   // M-mode IRQ enable
      .u_irq_enable_o(u_irq_enable),                   // U-mode IRQ enable
      .csr_irq_sec_i (csr_irq_sec),                    // Secure IRQ
      .sec_lvl_o     (sec_lvl_o),                      // Security level
      .mepc_o        (mepc),                           // M-mode exception PC
      .uepc_o        (uepc),                           // U-mode exception PC

      // Performance counter control
      .mcounteren_o(mcounteren),                       // Counter enable

      // Debug CSRs
      .debug_mode_i       (debug_mode),                // Debug mode active
      .debug_cause_i      (debug_cause),               // Debug cause
      .debug_csr_save_i   (debug_csr_save),            // Save CSRs for debug
      .depc_o             (depc),                      // Debug exception PC
      .debug_single_step_o(debug_single_step),         // Single step enable
      .debug_ebreakm_o    (debug_ebreakm),             // EBREAK in M-mode
      .debug_ebreaku_o    (debug_ebreaku),             // EBREAK in U-mode
      .trigger_match_o    (trigger_match),             // Trigger match

      .priv_lvl_o(current_priv_lvl),                   // Current privilege level

      // PMP configuration
      .pmp_addr_o(pmp_addr),                           // PMP addresses
      .pmp_cfg_o (pmp_cfg),                            // PMP configuration

      // PC values from pipeline stages
      .pc_if_i(pc_if),                                 // PC in IF
      .pc_id_i(pc_id),                                 // PC in ID
      .pc_ex_i(pc_ex),                                 // PC in EX

      // Exception/interrupt control from ID stage
      .csr_save_if_i     (csr_save_if),                // Save PC from IF
      .csr_save_id_i     (csr_save_id),                // Save PC from ID
      .csr_save_ex_i     (csr_save_ex),                // Save PC from EX
      .csr_restore_mret_i(csr_restore_mret_id),        // Restore from M-mode
      .csr_restore_uret_i(csr_restore_uret_id),        // Restore from U-mode

      .csr_restore_dret_i(csr_restore_dret_id),        // Restore from debug

      .csr_cause_i     (csr_cause),                    // Exception/interrupt cause
      .csr_save_cause_i(csr_save_cause),               // Save cause

      // Hardware loop CSRs (PULP)
      .hwlp_start_i(hwlp_start),                       // Loop start addresses
      .hwlp_end_i  (hwlp_end),                         // Loop end addresses
      .hwlp_cnt_i  (hwlp_cnt),                         // Loop counters

      // Performance counter events
      .mhpmevent_minstret_i    (mhpmevent_minstret),      // Instruction retired
      .mhpmevent_load_i        (mhpmevent_load),          // Load instruction
      .mhpmevent_store_i       (mhpmevent_store),         // Store instruction
      .mhpmevent_jump_i        (mhpmevent_jump),          // Jump instruction
      .mhpmevent_branch_i      (mhpmevent_branch),        // Branch instruction
      .mhpmevent_branch_taken_i(mhpmevent_branch_taken),  // Branch taken
      .mhpmevent_compressed_i  (mhpmevent_compressed),    // Compressed instruction
      .mhpmevent_jr_stall_i    (mhpmevent_jr_stall),      // Jump register stall
      .mhpmevent_imiss_i       (mhpmevent_imiss),         // Instruction miss
      .mhpmevent_ld_stall_i    (mhpmevent_ld_stall),      // Load stall
      .mhpmevent_pipe_stall_i  (mhpmevent_pipe_stall),    // Pipeline stall
      .apu_typeconflict_i      (perf_apu_type),           // APU type conflict
      .apu_contention_i        (perf_apu_cont),           // APU contention
      .apu_dep_i               (perf_apu_dep),            // APU dependency
      .apu_wb_i                (perf_apu_wb)              // APU writeback
  );

  ///////////////////////////////////////////////////////////////////////////////
  // CSR ACCESS WIRING
  ///////////////////////////////////////////////////////////////////////////////
  // Connect CSR access signals from EX stage to CSR registers module
  
  assign csr_addr = csr_addr_int;                      // CSR address from address generation
  assign csr_wdata = alu_operand_a_ex;                 // CSR write data from ALU operand A
  assign csr_op = csr_op_ex;                           // CSR operation from ID stage

  // Generate CSR address: use ALU operand B lower 12 bits when CSR access is active
  assign csr_addr_int = csr_num_e'(csr_access_ex ? alu_operand_b_ex[11:0] : '0);

  ///////////////////////////////////////////////////////////////////////////////
  // FLOATING-POINT REGISTER WRITE DETECTION
  ///////////////////////////////////////////////////////////////////////////////
  // Track writes to floating-point registers for FPU status updates
  // FP registers are identified by bit [5] = 1 when FPU enabled without ZFINX
  
  assign fregs_we     = (FPU == 1 & ZFINX == 0) ? ((regfile_alu_we_fw && regfile_alu_waddr_fw[5]) ||
                                                   (regfile_we_wb     && regfile_waddr_fw_wb_o[5]))
                                                : 1'b0;


  ///////////////////////////////////////////////////////////////////////////////
  // PHYSICAL MEMORY PROTECTION (PMP)
  ///////////////////////////////////////////////////////////////////////////////
  // Optional PMP unit for memory access control in secure configurations
  // Checks instruction and data accesses against configured memory regions
  
  generate
    if (PULP_SECURE && USE_PMP) begin : gen_pmp
      cv32e40p_pmp #(
          .N_PMP_ENTRIES(N_PMP_ENTRIES)                // Number of PMP entries
      ) pmp_unit_i (
          // Clock and reset
          .clk  (clk),
          .rst_n(rst_ni),

          .pmp_privil_mode_i(current_priv_lvl),        // Current privilege level

          // PMP configuration from CSRs
          .pmp_addr_i(pmp_addr),                       // PMP addresses
          .pmp_cfg_i (pmp_cfg),                        // PMP configuration

          // Data memory interface (LSU → PMP → Memory)
          .data_req_i (data_req_pmp),                  // Request from LSU
          .data_addr_i(data_addr_pmp),                 // Address from LSU
          .data_we_i  (data_we_o),                     // Write enable from LSU
          .data_gnt_o (data_gnt_pmp),                  // Grant to LSU

          .data_req_o    (data_req_o),                 // Request to memory
          .data_gnt_i    (data_gnt_i),                 // Grant from memory
          .data_addr_o   (data_addr_o),                // Address to memory
          .data_err_o    (data_err_pmp),               // PMP error to ID stage
          .data_err_ack_i(data_err_ack),               // Error acknowledge from ID

          // Instruction memory interface (IF → PMP → Memory)
          .instr_req_i (instr_req_pmp),                // Request from IF
          .instr_addr_i(instr_addr_pmp),               // Address from IF
          .instr_gnt_o (instr_gnt_pmp),                // Grant to IF

          .instr_req_o (instr_req_o),                  // Request to memory
          .instr_gnt_i (instr_gnt_i),                  // Grant from memory
          .instr_addr_o(instr_addr_o),                 // Address to memory
          .instr_err_o (instr_err_pmp)                 // PMP error to IF
      );
    end else begin : gen_no_pmp
      // When PMP is disabled, bypass PMP module: direct connections
      assign instr_req_o   = instr_req_pmp;
      assign instr_addr_o  = instr_addr_pmp;
      assign instr_gnt_pmp = instr_gnt_i;
      assign instr_err_pmp = 1'b0;

      assign data_req_o    = data_req_pmp;
      assign data_addr_o   = data_addr_pmp;
      assign data_gnt_pmp  = data_gnt_i;
      assign data_err_pmp  = 1'b0;
    end
  endgenerate


`ifdef CV32E40P_ASSERT_ON

  ///////////////////////////////////////////////////////////////////////////////
  // ASSERTIONS
  ///////////////////////////////////////////////////////////////////////////////
  // Formal verification assumptions and assertions
  
  //----------------------------------------------------------------------------
  // Assumptions on the environment
  //----------------------------------------------------------------------------

  generate
    if (COREV_CLUSTER) begin : gen_pulp_cluster_assumptions

      // Assumption: When pulp_clock_en_i = 0, no external events should occur
      // This ensures proper clock gating behavior in cluster mode
      property p_env_req_0;
        @(posedge clk_i) disable iff (!rst_ni) (pulp_clock_en_i == 1'b0) |-> (irq_i == 'b0) && (debug_req_i == 1'b0) &&
                                                                            (instr_rvalid_i == 1'b0) && (instr_gnt_i == 1'b0) &&
                                                                            (data_rvalid_i == 1'b0) && (data_gnt_i == 1'b0);
      endproperty

      a_env_req_0 :
      assume property (p_env_req_0);

      // Assumption: When core is not sleeping, clock must be enabled
      // Core sleep requires clock to remain active for proper wake-up
      property p_env_req_1;
        @(posedge clk_i) disable iff (!rst_ni) (core_sleep_o == 1'b0) |-> (pulp_clock_en_i == 1'b1);
      endproperty

      a_env_req_1 :
      assume property (p_env_req_1);

    end
  endgenerate

  //----------------------------------------------------------------------------
  // Assertions on core behavior
  //----------------------------------------------------------------------------

  generate
    if (!COREV_CLUSTER) begin : gen_no_pulp_cluster_assertions
      // Assertion: Check that a taken IRQ is actually enabled
      // Ensures we do not react to an IRQ that was just disabled in MIE
      property p_irq_enabled_0;
        @(posedge clk) disable iff (!rst_ni) (pc_set && (pc_mux_id == PC_EXCEPTION) && (exc_pc_mux_id == EXC_PC_IRQ)) |->
         (cs_registers_i.mie_n[exc_cause] && cs_registers_i.mstatus_q.mie);
      endproperty

      a_irq_enabled_0 :
      assert property (p_irq_enabled_0);

      // Assertion: Check that taking an IRQ disables mstatus.mie
      // After taking IRQ, verify the cause is enabled and MIE gets disabled
      property p_irq_enabled_1;
        @(posedge clk) disable iff (!rst_ni) (pc_set && (pc_mux_id == PC_EXCEPTION) && (exc_pc_mux_id == EXC_PC_IRQ)) |=>
         (cs_registers_i.mcause_q[5] && cs_registers_i.mie_q[cs_registers_i.mcause_q[4:0]] && !cs_registers_i.mstatus_q.mie);
      endproperty

      a_irq_enabled_1 :
      assert property (p_irq_enabled_1);
    end
  endgenerate

  generate
    if (!COREV_PULP) begin : gen_no_pulp_xpulp_assertions

      // Assertions for MEPC correctness on illegal instructions, ECALL, EBRK
      // These checks are excluded for PULP mode due to different hardware loop behavior

      // Track first occurrence of illegal instruction, ECALL, EBRK in decode stage
      logic        first_illegal_found;
      logic        first_ecall_found;
      logic        first_ebrk_found;
      logic [31:0] expected_illegal_mepc;
      logic [31:0] expected_ecall_mepc;
      logic [31:0] expected_ebrk_mepc;

      always_ff @(posedge clk, negedge rst_ni) begin
        if (rst_ni == 1'b0) begin
          first_illegal_found   <= 1'b0;
          first_ecall_found     <= 1'b0;
          first_ebrk_found      <= 1'b0;
          expected_illegal_mepc <= 32'b0;
          expected_ecall_mepc   <= 32'b0;
          expected_ebrk_mepc    <= 32'b0;
        end else begin
          // Capture PC of first illegal instruction (outside debug mode)
          if (!first_illegal_found && is_decoding && id_valid && id_stage_i.illegal_insn_dec && !id_stage_i.controller_i.debug_mode_n) begin
            first_illegal_found   <= 1'b1;
            expected_illegal_mepc <= pc_id;
          end
          // Capture PC of first ECALL instruction (outside debug mode)
          if (!first_ecall_found && is_decoding && id_valid && id_stage_i.ecall_insn_dec && !id_stage_i.controller_i.debug_mode_n) begin
            first_ecall_found   <= 1'b1;
            expected_ecall_mepc <= pc_id;
          end
          // Capture PC of first EBRK instruction (not entering debug)
          if (!first_ebrk_found && is_decoding && id_valid && id_stage_i.ebrk_insn_dec && (id_stage_i.controller_i.ctrl_fsm_ns != DBG_FLUSH)) begin
            first_ebrk_found   <= 1'b1;
            expected_ebrk_mepc <= pc_id;
          end
        end
      end

      // Track when MEPC is actually written with the exception cause
      logic        first_cause_illegal_found;
      logic        first_cause_ecall_found;
      logic        first_cause_ebrk_found;
      logic [31:0] actual_illegal_mepc;
      logic [31:0] actual_ecall_mepc;
      logic [31:0] actual_ebrk_mepc;

      always_ff @(posedge clk, negedge rst_ni) begin
        if (rst_ni == 1'b0) begin
          first_cause_illegal_found <= 1'b0;
          first_cause_ecall_found   <= 1'b0;
          first_cause_ebrk_found    <= 1'b0;
          actual_illegal_mepc       <= 32'b0;
          actual_ecall_mepc         <= 32'b0;
          actual_ebrk_mepc          <= 32'b0;
        end else begin
          // Capture MEPC when illegal instruction exception is saved
          if (!first_cause_illegal_found && (cs_registers_i.csr_cause_i == {
                1'b0, EXC_CAUSE_ILLEGAL_INSN
              }) && csr_save_cause) begin
            first_cause_illegal_found <= 1'b1;
            actual_illegal_mepc       <= cs_registers_i.mepc_n;
          end
          // Capture MEPC when ECALL exception is saved
          if (!first_cause_ecall_found && (cs_registers_i.csr_cause_i == {
                1'b0, EXC_CAUSE_ECALL_MMODE
              }) && csr_save_cause) begin
            first_cause_ecall_found <= 1'b1;
            actual_ecall_mepc       <= cs_registers_i.mepc_n;
          end
          // Capture MEPC when breakpoint exception is saved
          if (!first_cause_ebrk_found && (cs_registers_i.csr_cause_i == {
                1'b0, EXC_CAUSE_BREAKPOINT
              }) && csr_save_cause) begin
            first_cause_ebrk_found <= 1'b1;
            actual_ebrk_mepc       <= cs_registers_i.mepc_n;
          end
        end
      end

      // Assertion: Verify MEPC contains PC of illegal instruction
      property p_illegal_mepc;
        @(posedge clk) disable iff (!rst_ni) (first_illegal_found && first_cause_illegal_found) |=> (expected_illegal_mepc == actual_illegal_mepc);
      endproperty

      a_illegal_mepc :
      assert property (p_illegal_mepc);

      // Assertion: Verify MEPC contains PC of ECALL instruction
      property p_ecall_mepc;
        @(posedge clk) disable iff (!rst_ni) (first_ecall_found && first_cause_ecall_found) |=> (expected_ecall_mepc == actual_ecall_mepc);
      endproperty

      a_ecall_mepc :
      assert property (p_ecall_mepc);

      // Assertion: Verify MEPC contains PC of EBRK instruction
      property p_ebrk_mepc;
        @(posedge clk) disable iff (!rst_ni) (first_ebrk_found && first_cause_ebrk_found) |=> (expected_ebrk_mepc == actual_ebrk_mepc);
      endproperty

      a_ebrk_mepc :
      assert property (p_ebrk_mepc);

    end
  endgenerate

  //----------------------------------------------------------------------------
  // Debug single-step assertion
  //----------------------------------------------------------------------------
  
  // Assertion: Single step mode only decodes one instruction
  // When single step is enabled, after decoding one instruction in non-debug mode,
  // the next instruction decode must occur in debug mode
  logic inst_taken;
  assign inst_taken = id_valid && is_decoding;

  a_single_step :
  assert property
  (
    @(posedge clk) disable iff (!rst_ni)
    (inst_taken && debug_single_step && ~debug_mode)
    ##1 inst_taken [->1]
    |-> (debug_mode && debug_single_step));

`endif

endmodule
