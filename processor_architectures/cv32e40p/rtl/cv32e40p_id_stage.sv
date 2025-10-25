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
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Instruction Decode Stage                                   //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decode stage of the core. It decodes the instructions      //
//                 and hosts the register file.                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// CV32E40P INSTRUCTION DECODE (ID) STAGE
////////////////////////////////////////////////////////////////////////////////
//
// The ID stage is the heart of instruction processing in the CV32E40P core.
// It performs instruction decoding, register file access, operand selection,
// hazard detection, and pipeline control.
//
// KEY RESPONSIBILITIES:
// 1. Instruction Decoding
//    - Decodes RV32IMC instructions using cv32e40p_decoder module
//    - Supports PULP ISA extensions (post-increment, hardware loops, etc.)
//    - Handles compressed (16-bit) instructions
//    - Detects illegal instructions
//
// 2. Register File Management
//    - Instantiates 31x32-bit general-purpose register file (x1-x31, x0=0)
//    - Performs register reads for source operands (rs1, rs2, rs3 for APU)
//    - Handles register write forwarding from EX and WB stages
//    - Manages FPU register file interface (if FPU enabled)
//
// 3. Operand Generation
//    - Selects ALU operands (register values or immediates)
//    - Generates immediate values from instruction fields
//    - Handles special addressing modes (post-increment for loads/stores)
//    - Provides operands for multiplier and APU/FPU
//
// 4. Hazard Detection and Stalling
//    - Detects RAW (Read-After-Write) hazards
//    - Implements data forwarding from EX and WB stages
//    - Stalls pipeline when hazards cannot be resolved by forwarding
//    - Handles multi-cycle instruction dependencies
//
// 5. Control Flow
//    - Processes jump and branch instructions
//    - Calculates jump targets
//    - Interfaces with controller for exception/interrupt handling
//    - Manages hardware loop control (PULP extension)
//
// 6. Exception and Interrupt Handling
//    - Detects exceptions (illegal instruction, misaligned access, etc.)
//    - Interfaces with interrupt controller
//    - Manages debug mode entry/exit
//    - Handles CSR instructions
//
// 7. Pipeline Control
//    - Implements ID/EX pipeline register
//    - Manages pipeline flush on control flow changes
//    - Coordinates with IF, EX, and WB stages
//    - Handles pipeline stalls and bubbles
//
// PIPELINE STRUCTURE:
//   IF Stage → [IF/ID Register] → ID Stage → [ID/EX Register] → EX Stage
//
// The ID stage receives instructions from IF stage, decodes them, reads
// register operands, and forwards the decoded information to EX stage.
//
////////////////////////////////////////////////////////////////////////////////

module cv32e40p_id_stage
  import cv32e40p_pkg::*;
  import cv32e40p_apu_core_pkg::*;
#(
    parameter COREV_PULP =  1,           // PULP ISA extensions (hardware loops, post-increment, etc.)
    parameter COREV_CLUSTER = 0,         // Cluster-specific features (cv.elw instruction)
    parameter N_HWLP = 2,                // Number of hardware loop registers (0, 1, or 2)
    parameter N_HWLP_BITS = $clog2(N_HWLP),
    parameter PULP_SECURE = 0,           // Security features (U-mode, PMP)
    parameter USE_PMP = 0,               // Physical Memory Protection
    parameter A_EXTENSION = 0,           // Atomic instructions extension
    parameter APU = 0,                   // Auxiliary Processing Unit (shared FPU/coprocessor)
    parameter FPU = 0,                   // Floating-Point Unit (0=none, 1=enabled)
    parameter FPU_ADDMUL_LAT = 0,        // FPU add/mul latency
    parameter FPU_OTHERS_LAT = 0,        // FPU other operations latency
    parameter ZFINX = 0,                 // FP in integer registers (0=FP regs, 1=integer regs)
    parameter APU_NARGS_CPU = 3,         // Number of APU operands
    parameter APU_WOP_CPU = 6,           // APU operation width
    parameter APU_NDSFLAGS_CPU = 15,     // APU dynamic status flags
    parameter APU_NUSFLAGS_CPU = 5,      // APU user status flags
    parameter DEBUG_TRIGGER_EN = 1       // Hardware trigger support (breakpoints)
) (
    ///////////////////////////////////////////////////////////////////
    // CLOCK AND RESET
    ///////////////////////////////////////////////////////////////////
    input logic clk,              // Gated clock (clock-gated for power saving)
    input logic clk_ungated_i,    // Ungated clock (always running)
    input logic rst_n,            // Active-low reset

    input logic scan_cg_en_i,     // Scan mode clock gate enable (for DFT)

    ///////////////////////////////////////////////////////////////////
    // CORE CONTROL SIGNALS
    ///////////////////////////////////////////////////////////////////
    input  logic fetch_enable_i,   // Core is enabled to fetch instructions
    output logic ctrl_busy_o,      // Controller is busy (processing exception/interrupt)
    output logic is_decoding_o,    // ID stage is actively decoding an instruction

    ///////////////////////////////////////////////////////////////////
    // INTERFACE TO IF STAGE
    ///////////////////////////////////////////////////////////////////
    input  logic        instr_valid_i,      // Instruction from IF is valid
    input  logic [31:0] instr_rdata_i,      // Instruction data (from IF/ID pipeline register)
    output logic        instr_req_o,        // ID stage requests next instruction
    input  logic        is_compressed_i,    // Instruction is compressed (16-bit)
    input  logic        illegal_c_insn_i,   // Illegal compressed instruction

    ///////////////////////////////////////////////////////////////////
    // CONTROL FLOW (JUMPS AND BRANCHES)
    ///////////////////////////////////////////////////////////////////
    output logic        branch_in_ex_o,              // Branch instruction in EX stage
    input  logic        branch_decision_i,           // Branch taken decision from EX
    output logic [31:0] jump_target_o,               // Jump/branch target address
    output logic [ 1:0] ctrl_transfer_insn_in_dec_o, // Control transfer instruction type

    ///////////////////////////////////////////////////////////////////
    // PROGRAM COUNTER CONTROL
    ///////////////////////////////////////////////////////////////////
    output logic       clear_instr_valid_o,  // Clear IF/ID pipeline register
    output logic       pc_set_o,             // Set PC to new value
    output logic [3:0] pc_mux_o,             // PC source select
    output logic [2:0] exc_pc_mux_o,         // Exception PC source
    output logic [1:0] trap_addr_mux_o,      // Trap handler address select

    input logic is_fetch_failed_i,   // Instruction fetch failed (bus error)
    input logic [31:0] pc_id_i,      // Current PC in ID stage

    ///////////////////////////////////////////////////////////////////
    // PIPELINE CONTROL (STALLS AND VALID SIGNALS)
    ///////////////////////////////////////////////////////////////////
    output logic halt_if_o,     // Halt IF stage (stop fetching)

    output logic id_ready_o,    // ID stage ready for next instruction
    input  logic ex_ready_i,    // EX stage ready for next instruction
    input  logic wb_ready_i,    // WB stage ready for next instruction

    output logic id_valid_o,    // ID stage output is valid
    input  logic ex_valid_i,    // EX stage output is valid

    // Pipeline ID/EX
    output logic [31:0] pc_ex_o,

    output logic [31:0] alu_operand_a_ex_o,
    output logic [31:0] alu_operand_b_ex_o,
    output logic [31:0] alu_operand_c_ex_o,
    output logic [ 4:0] bmask_a_ex_o,
    output logic [ 4:0] bmask_b_ex_o,
    output logic [ 1:0] imm_vec_ext_ex_o,
    output logic [ 1:0] alu_vec_mode_ex_o,

    output logic [5:0] regfile_waddr_ex_o,
    output logic       regfile_we_ex_o,

    output logic [5:0] regfile_alu_waddr_ex_o,
    output logic       regfile_alu_we_ex_o,

    ///////////////////////////////////////////////////////////////////
    // ALU CONTROL SIGNALS
    ///////////////////////////////////////////////////////////////////
    output logic              alu_en_ex_o,           // ALU operation enable
    output alu_opcode_e       alu_operator_ex_o,     // ALU operation select
    output logic              alu_is_clpx_ex_o,      // Complex number operation (PULP)
    output logic              alu_is_subrot_ex_o,    // Sub-rotation operation (PULP)
    output logic        [1:0] alu_clpx_shift_ex_o,   // Complex number shift amount

    ///////////////////////////////////////////////////////////////////
    // MULTIPLIER CONTROL SIGNALS
    ///////////////////////////////////////////////////////////////////
    output mul_opcode_e        mult_operator_ex_o,       // Multiplier operation
    output logic        [31:0] mult_operand_a_ex_o,      // Multiplier operand A
    output logic        [31:0] mult_operand_b_ex_o,      // Multiplier operand B
    output logic        [31:0] mult_operand_c_ex_o,      // Multiplier operand C (accumulate)
    output logic               mult_en_ex_o,             // Multiplier enable
    output logic               mult_sel_subword_ex_o,    // Sub-word operation select
    output logic        [ 1:0] mult_signed_mode_ex_o,    // Signed/unsigned mode
    output logic        [ 4:0] mult_imm_ex_o,            // Immediate for multiply-add

    // Dot product and complex multiply (PULP extensions)
    output logic [31:0] mult_dot_op_a_ex_o,       // Dot product operand A
    output logic [31:0] mult_dot_op_b_ex_o,       // Dot product operand B
    output logic [31:0] mult_dot_op_c_ex_o,       // Dot product operand C
    output logic [ 1:0] mult_dot_signed_ex_o,     // Dot product signed mode
    output logic        mult_is_clpx_ex_o,        // Complex multiply
    output logic [ 1:0] mult_clpx_shift_ex_o,     // Complex multiply shift
    output logic        mult_clpx_img_ex_o,       // Complex multiply imaginary part

    ///////////////////////////////////////////////////////////////////
    // APU/FPU INTERFACE
    ///////////////////////////////////////////////////////////////////
    output logic                              apu_en_ex_o,        // APU operation enable
    output logic [     APU_WOP_CPU-1:0]       apu_op_ex_o,        // APU operation code
    output logic [                 1:0]       apu_lat_ex_o,       // APU latency
    output logic [   APU_NARGS_CPU-1:0][31:0] apu_operands_ex_o,  // APU operands (up to 3)
    output logic [APU_NDSFLAGS_CPU-1:0]       apu_flags_ex_o,     // APU dynamic flags
    output logic [                 5:0]       apu_waddr_ex_o,     // APU result write address

    // APU dependency tracking
    output logic [2:0][5:0] apu_read_regs_o,         // APU read register addresses
    output logic [2:0]      apu_read_regs_valid_o,   // APU read registers valid
    input  logic            apu_read_dep_i,          // APU read dependency detected
    input  logic            apu_read_dep_for_jalr_i, // APU read dependency for JALR
    output logic [1:0][5:0] apu_write_regs_o,        // APU write register addresses
    output logic [1:0]      apu_write_regs_valid_o,  // APU write registers valid
    input  logic            apu_write_dep_i,         // APU write dependency detected
    output logic            apu_perf_dep_o,          // APU performance counter dependency
    input  logic            apu_busy_i,              // APU is busy

    // FPU status (from CSR)
    input logic            fs_off_i,   // FPU disabled (mstatus.FS = OFF)
    input logic [C_RM-1:0] frm_i,      // FP rounding mode (from fcsr.frm)

    ///////////////////////////////////////////////////////////////////
    // CSR INTERFACE
    ///////////////////////////////////////////////////////////////////
    output logic              csr_access_ex_o,       // CSR access in EX stage
    output csr_opcode_e       csr_op_ex_o,           // CSR operation (read/write/set/clear)
    input  PrivLvl_t          current_priv_lvl_i,    // Current privilege level
    output logic              csr_irq_sec_o,         // Secure interrupt (M-mode)
    output logic        [5:0] csr_cause_o,           // Exception/interrupt cause
    output logic              csr_save_if_o,         // Save PC from IF stage
    output logic              csr_save_id_o,         // Save PC from ID stage
    output logic              csr_save_ex_o,         // Save PC from EX stage
    output logic              csr_restore_mret_id_o, // MRET in ID stage
    output logic              csr_restore_uret_id_o, // URET in ID stage
    output logic              csr_restore_dret_id_o, // DRET in ID stage
    output logic              csr_save_cause_o,      // Save exception cause

    ///////////////////////////////////////////////////////////////////
    // HARDWARE LOOP INTERFACE (PULP extension)
    ///////////////////////////////////////////////////////////////////
    output logic [N_HWLP-1:0][31:0] hwlp_start_o,   // Hardware loop start addresses
    output logic [N_HWLP-1:0][31:0] hwlp_end_o,     // Hardware loop end addresses
    output logic [N_HWLP-1:0][31:0] hwlp_cnt_o,     // Hardware loop counters
    output logic                    hwlp_jump_o,    // Hardware loop jump taken
    output logic [      31:0]       hwlp_target_o,  // Hardware loop target address

    ///////////////////////////////////////////////////////////////////
    // LOAD/STORE UNIT INTERFACE
    ///////////////////////////////////////////////////////////////////
    output logic       data_req_ex_o,          // Data memory request
    output logic       data_we_ex_o,           // Data memory write enable
    output logic [1:0] data_type_ex_o,         // Data access size (byte/half/word)
    output logic [1:0] data_sign_ext_ex_o,     // Sign extension for loads
    output logic [1:0] data_reg_offset_ex_o,   // Register offset for indexed loads
    output logic       data_load_event_ex_o,   // Load event (cv.elw instruction)

    output logic data_misaligned_ex_o,  // Misaligned data access

    output logic prepost_useincr_ex_o,  // Post-increment addressing mode
    input  logic data_misaligned_i,     // Misaligned access detected (from LSU)
    input  logic data_err_i,            // Data access error (bus error)
    output logic data_err_ack_o,        // Acknowledge data error

    output logic [5:0] atop_ex_o,  // Atomic operation code (A extension)

    ///////////////////////////////////////////////////////////////////
    // INTERRUPT INTERFACE
    ///////////////////////////////////////////////////////////////////
    input  logic [31:0] irq_i,           // Interrupt request lines
    input  logic        irq_sec_i,       // Secure interrupt (M-mode only)
    input  logic [31:0] mie_bypass_i,    // MIE CSR bypass value
    output logic [31:0] mip_o,           // MIP CSR value (interrupt pending)
    input  logic        m_irq_enable_i,  // M-mode interrupts enabled
    input  logic        u_irq_enable_i,  // U-mode interrupts enabled
    output logic        irq_ack_o,       // Interrupt acknowledged
    output logic [ 4:0] irq_id_o,        // Interrupt ID
    output logic [ 4:0] exc_cause_o,     // Exception cause

    ///////////////////////////////////////////////////////////////////
    // DEBUG INTERFACE
    ///////////////////////////////////////////////////////////////////
    output logic       debug_mode_o,           // Core in debug mode
    output logic [2:0] debug_cause_o,          // Debug entry cause
    output logic       debug_csr_save_o,       // Save CSRs on debug entry
    input  logic       debug_req_i,            // Debug request (from debug module)
    input  logic       debug_single_step_i,    // Single-step mode enabled
    input  logic       debug_ebreakm_i,        // EBREAK in M-mode enters debug
    input  logic       debug_ebreaku_i,        // EBREAK in U-mode enters debug
    input  logic       trigger_match_i,        // Hardware trigger match
    output logic       debug_p_elw_no_sleep_o, // No sleep on cv.elw in debug
    output logic       debug_havereset_o,      // Core has been reset
    output logic       debug_running_o,        // Core is running
    output logic       debug_halted_o,         // Core is halted

    ///////////////////////////////////////////////////////////////////
    // WAKEUP SIGNAL
    ///////////////////////////////////////////////////////////////////
    output logic wake_from_sleep_o,  // Wake from sleep (WFI instruction)

    ///////////////////////////////////////////////////////////////////
    // FORWARDING INPUTS (from EX and WB stages)
    ///////////////////////////////////////////////////////////////////
    // Writeback stage forwarding
    input logic [ 5:0] regfile_waddr_wb_i,     // WB write address
    input logic        regfile_we_wb_i,        // WB write enable
    input logic        regfile_we_wb_power_i,  // WB write enable (power signal)
    input logic [31:0] regfile_wdata_wb_i,     // WB write data

    // EX stage forwarding (ALU path)
    input logic [ 5:0] regfile_alu_waddr_fw_i,     // EX ALU write address
    input logic        regfile_alu_we_fw_i,        // EX ALU write enable
    input logic        regfile_alu_we_fw_power_i,  // EX ALU write enable (power)
    input logic [31:0] regfile_alu_wdata_fw_i,     // EX ALU write data

    ///////////////////////////////////////////////////////////////////
    // HAZARD SIGNALS FROM ALU
    ///////////////////////////////////////////////////////////////////
    input  logic        mult_multicycle_i,    // Multi-cycle multiplier operation

    ///////////////////////////////////////////////////////////////////
    // PERFORMANCE COUNTERS
    ///////////////////////////////////////////////////////////////////
    output logic mhpmevent_minstret_o,        // Instruction retired
    output logic mhpmevent_load_o,            // Load instruction
    output logic mhpmevent_store_o,           // Store instruction
    output logic mhpmevent_jump_o,            // Jump instruction
    output logic mhpmevent_branch_o,          // Branch instruction
    output logic mhpmevent_branch_taken_o,    // Branch taken
    output logic mhpmevent_compressed_o,      // Compressed instruction
    output logic mhpmevent_jr_stall_o,        // Jump register stall
    output logic mhpmevent_imiss_o,           // Instruction cache miss
    output logic mhpmevent_ld_stall_o,        // Load-use hazard stall
    output logic mhpmevent_pipe_stall_o,      // Pipeline stall

    input logic        perf_imiss_i,     // Instruction miss from IF stage
    input logic [31:0] mcounteren_i      // Counter enable (for U-mode access)
);

  ///////////////////////////////////////////////////////////////////
  // INSTRUCTION FIELD EXTRACTION PARAMETERS
  ///////////////////////////////////////////////////////////////////
  // Bit positions for extracting register addresses from instruction
  localparam REG_S1_MSB = 19;  // rs1 (source register 1) [19:15]
  localparam REG_S1_LSB = 15;

  localparam REG_S2_MSB = 24;  // rs2 (source register 2) [24:20]
  localparam REG_S2_LSB = 20;

  localparam REG_S4_MSB = 31;  // rs4 (source register 4, for special instructions) [31:27]
  localparam REG_S4_LSB = 27;

  localparam REG_D_MSB = 11;   // rd (destination register) [11:7]
  localparam REG_D_LSB = 7;

  ///////////////////////////////////////////////////////////////////
  // INTERNAL SIGNALS
  ///////////////////////////////////////////////////////////////////
  
  logic [31:0] instr;  // Current instruction being decoded

  ///////////////////////////////////////////////////////////////////
  // DECODER/CONTROLLER CONTROL SIGNALS
  ///////////////////////////////////////////////////////////////////
  logic        deassert_we;  // Deassert write enable (for pipeline flush)

  // Exception and special instruction decode signals
  logic        illegal_insn_dec;   // Illegal instruction detected
  logic        ebrk_insn_dec;      // EBREAK instruction
  logic        mret_insn_dec;      // MRET (return from M-mode trap)
  logic        uret_insn_dec;      // URET (return from U-mode trap)
  logic        dret_insn_dec;      // DRET (return from Debug mode)
  logic        ecall_insn_dec;     // ECALL (environment call)
  logic        wfi_insn_dec;       // WFI (wait for interrupt)
  logic        fencei_insn_dec;    // FENCE.I (instruction fence)

  // Register usage signals (for hazard detection)
  logic        rega_used_dec;      // Instruction uses rs1
  logic        regb_used_dec;      // Instruction uses rs2
  logic        regc_used_dec;      // Instruction uses rs3 (for APU/stores)

  // Branch and control transfer signals
  logic        branch_taken_ex;              // Branch was taken in EX stage
  logic [ 1:0] ctrl_transfer_insn_in_id;     // Control transfer instruction type in ID
  logic [ 1:0] ctrl_transfer_insn_in_dec;    // Control transfer instruction type decoded

  // Pipeline stall signals
  logic        misaligned_stall;   // Stall due to misaligned memory access
  logic        jr_stall;           // Stall due to jump register hazard
  logic        load_stall;         // Stall due to load-use hazard
  logic        csr_apu_stall;      // Stall due to CSR or APU dependency
  logic        hwlp_mask;          // Hardware loop mask signal
  logic        halt_id;            // Halt ID stage
  logic        halt_if;            // Halt IF stage

  logic        debug_wfi_no_sleep; // Prevent sleep on WFI in debug mode

  ///////////////////////////////////////////////////////////////////
  // IMMEDIATE VALUE GENERATION
  ///////////////////////////////////////////////////////////////////
  // Decoded and sign-extended immediate values for different instruction types
  logic [31:0] imm_i_type;         // I-type immediate (12-bit sign-extended)
  logic [31:0] imm_iz_type;        // I-type immediate (zero-extended, for shifts)
  logic [31:0] imm_s_type;         // S-type immediate (store offset)
  logic [31:0] imm_sb_type;        // SB-type immediate (branch offset)
  logic [31:0] imm_u_type;         // U-type immediate (upper immediate)
  logic [31:0] imm_uj_type;        // UJ-type immediate (jump offset)
  logic [31:0] imm_z_type;         // Z-type immediate (CSR immediate)
  logic [31:0] imm_s2_type;        // S2-type immediate (PULP)
  logic [31:0] imm_bi_type;        // BI-type immediate (PULP)
  logic [31:0] imm_s3_type;        // S3-type immediate (PULP)
  logic [31:0] imm_vs_type;        // VS-type immediate (PULP vector)
  logic [31:0] imm_vu_type;        // VU-type immediate (PULP vector)
  logic [31:0] imm_shuffleb_type;  // Shuffle byte immediate (PULP)
  logic [31:0] imm_shuffleh_type;  // Shuffle halfword immediate (PULP)
  logic [31:0] imm_shuffle_type;   // Shuffle immediate (PULP)
  logic [31:0] imm_clip_type;      // Clip immediate (PULP)

  logic [31:0] imm_a;              // Immediate for operand A
  logic [31:0] imm_b;              // Immediate for operand B

  logic [31:0] jump_target;        // Calculated jump target address

  ///////////////////////////////////////////////////////////////////
  // INTERRUPT CONTROLLER INTERFACE
  ///////////////////////////////////////////////////////////////////
  // Signals between controller and interrupt controller
  logic        irq_req_ctrl;   // Interrupt request to controller
  logic        irq_sec_ctrl;   // Secure interrupt (M-mode only)
  logic        irq_wu_ctrl;    // Wake-up interrupt
  logic [ 4:0] irq_id_ctrl;    // Interrupt ID

  ///////////////////////////////////////////////////////////////////
  // REGISTER FILE INTERFACE
  ///////////////////////////////////////////////////////////////////
  logic [ 5:0] regfile_addr_ra_id;  // Register file read address A (rs1)
  logic [ 5:0] regfile_addr_rb_id;  // Register file read address B (rs2)
  logic [ 5:0] regfile_addr_rc_id;  // Register file read address C (rs3/rs2 for stores)

  // FPU register file indicators (bit 5 = 1 for FP regs when ZFINX=0)
  logic        regfile_fp_a;   // Operand A is FP register
  logic        regfile_fp_b;   // Operand B is FP register
  logic        regfile_fp_c;   // Operand C is FP register
  logic        regfile_fp_d;   // Destination is FP register

  logic [ 5:0] regfile_waddr_id;      // Register file write address (rd)
  logic [ 5:0] regfile_alu_waddr_id;  // ALU result write address

  logic        regfile_alu_we_id;      // ALU write enable for ID stage
  logic        regfile_alu_we_dec_id;  // ALU write enable from decoder

  logic [31:0] regfile_data_ra_id;  // Register file data output for rs1
  logic [31:0] regfile_data_rb_id;  // Register file data output for rs2
  logic [31:0] regfile_data_rc_id;  // Register file data output for rs3/rs2

  ///////////////////////////////////////////////////////////////////
  // ALU CONTROL SIGNALS
  ///////////////////////////////////////////////////////////////////
  logic        alu_en;          // ALU operation enable
  alu_opcode_e alu_operator;    // ALU operation to perform (ADD, SUB, XOR, etc.)
  logic [2:0]  alu_op_a_mux_sel;  // Operand A source select (register/immediate/PC)
  logic [2:0]  alu_op_b_mux_sel;  // Operand B source select (register/immediate)
  logic [1:0]  alu_op_c_mux_sel;  // Operand C source select (for PULP instructions)
  logic [1:0]  regc_mux;          // Register C source multiplexer

  logic [0:0]  imm_a_mux_sel;     // Immediate A multiplexer select
  logic [3:0]  imm_b_mux_sel;     // Immediate B multiplexer select (supports multiple formats)
  logic [1:0]  ctrl_transfer_target_mux_sel;  // Control transfer target select (for jumps/branches)

  ///////////////////////////////////////////////////////////////////
  // MULTIPLIER CONTROL SIGNALS
  ///////////////////////////////////////////////////////////////////
  mul_opcode_e mult_operator;       // Multiplication operation selection (MUL, MULH, MULHSU, etc.)
  logic        mult_en;             // Multiplier is used instead of ALU
  logic        mult_int_en;         // Use integer multiplier (vs FP multiplier)
  logic        mult_sel_subword;    // Select subword for 16-bit/8-bit multiplications
  logic [1:0]  mult_signed_mode;    // Signed mode (00=UxU, 01=SxU, 10=UxS, 11=SxS)
  logic        mult_dot_en;         // Use dot product operation (PULP extension)
  logic [1:0]  mult_dot_signed;     // Signed mode for dot products (mixed types possible)

  ///////////////////////////////////////////////////////////////////
  // FPU CONTROL SIGNALS
  ///////////////////////////////////////////////////////////////////
  logic [cv32e40p_fpu_pkg::FP_FORMAT_BITS-1:0] fpu_src_fmt;  // Source format (FP32, FP64, FP16, etc.)
  logic [cv32e40p_fpu_pkg::FP_FORMAT_BITS-1:0] fpu_dst_fmt;  // Destination format
  logic [cv32e40p_fpu_pkg::INT_FORMAT_BITS-1:0] fpu_int_fmt; // Integer format for conversions

  ///////////////////////////////////////////////////////////////////
  // APU (AUXILIARY PROCESSING UNIT) SIGNALS
  ///////////////////////////////////////////////////////////////////
  logic                        apu_en;              // APU operation enable
  logic [APU_WOP_CPU-1:0]      apu_op;              // APU operation code
  logic [1:0]                  apu_lat;             // APU operation latency
  logic [APU_NARGS_CPU-1:0][31:0] apu_operands;     // APU operand array
  logic [APU_NDSFLAGS_CPU-1:0] apu_flags;           // APU data-side flags
  logic [5:0]                  apu_waddr;           // APU write-back address

  logic [2:0][5:0] apu_read_regs;         // APU read register addresses
  logic [2:0]      apu_read_regs_valid;   // APU read register valid flags
  logic [1:0][5:0] apu_write_regs;        // APU write register addresses
  logic [1:0]      apu_write_regs_valid;  // APU write register valid flags

  logic        apu_stall;       // Stall due to APU dependency
  logic [2:0]  fp_rnd_mode;     // FP rounding mode (RNE, RTZ, RDN, RUP, RMM)

  ///////////////////////////////////////////////////////////////////
  // REGISTER WRITE CONTROL
  ///////////////////////////////////////////////////////////////////
  logic regfile_we_id;                  // Register write enable
  logic regfile_alu_waddr_mux_sel;      // Select between normal and ALU write address

  ///////////////////////////////////////////////////////////////////
  // DATA MEMORY CONTROL SIGNALS
  ///////////////////////////////////////////////////////////////////
  logic        data_we_id;           // Data memory write enable (1=store, 0=load)
  logic [1:0]  data_type_id;         // Data type (00=byte, 01=half, 10=word)
  logic [1:0]  data_sign_ext_id;     // Sign extension control for loads
  logic [1:0]  data_reg_offset_id;   // Register offset for indexed addressing
  logic        data_req_id;          // Data memory request
  logic        data_load_event_id;   // Load event instruction (cv.elw - event load word)

  // Atomic memory instruction (A extension)
  logic [5:0] atop_id;  // Atomic operation type (SWAP, ADD, XOR, AND, OR, MIN, MAX, etc.)

  ///////////////////////////////////////////////////////////////////
  // HARDWARE LOOP CONTROL SIGNALS (PULP Extension)
  ///////////////////////////////////////////////////////////////////
  logic [N_HWLP_BITS-1:0] hwlp_regid;           // Hardware loop register ID
  logic [2:0]             hwlp_we;              // Hardware loop write enable
  logic [2:0]             hwlp_we_masked;       // Masked write enable
  logic [1:0]             hwlp_target_mux_sel;  // Loop target multiplexer select
  logic [1:0]             hwlp_start_mux_sel;   // Loop start address select
  logic                   hwlp_cnt_mux_sel;     // Loop counter select

  logic [31:0]      hwlp_start;       // Hardware loop start address
  logic [31:0]      hwlp_end;         // Hardware loop end address
  logic [31:0]      hwlp_cnt;         // Hardware loop counter value
  logic [N_HWLP-1:0] hwlp_dec_cnt;    // Hardware loop counter decrement
  logic             hwlp_valid;       // Hardware loop instruction valid

  ///////////////////////////////////////////////////////////////////
  // CSR CONTROL SIGNALS
  ///////////////////////////////////////////////////////////////////
  logic        csr_access;  // CSR access in progress
  csr_opcode_e csr_op;      // CSR operation (CSRRW, CSRRS, CSRRC, etc.)
  logic        csr_status;  // CSR status signal

  logic        prepost_useincr;  // Use post-increment addressing (PULP extension)

  ///////////////////////////////////////////////////////////////////
  // DATA FORWARDING CONTROL
  ///////////////////////////////////////////////////////////////////
  // Forwarding multiplexer selects (00=register file, 01=EX, 10=WB)
  logic [1:0] operand_a_fw_mux_sel;  // Operand A forwarding select
  logic [1:0] operand_b_fw_mux_sel;  // Operand B forwarding select
  logic [1:0] operand_c_fw_mux_sel;  // Operand C forwarding select

  // Forwarded operand values after multiplexing
  logic [31:0] operand_a_fw_id;  // Operand A after forwarding
  logic [31:0] operand_b_fw_id;  // Operand B after forwarding
  logic [31:0] operand_c_fw_id;  // Operand C after forwarding

  // Final operand values
  logic [31:0] operand_b;      // Operand B (scalar)
  logic [31:0] operand_b_vec;  // Operand B (vector/SIMD)
  logic [31:0] operand_c;      // Operand C (scalar)
  logic [31:0] operand_c_vec;  // Operand C (vector/SIMD)

  // Final ALU operands
  logic [31:0] alu_operand_a;  // Final ALU operand A
  logic [31:0] alu_operand_b;  // Final ALU operand B
  logic [31:0] alu_operand_c;  // Final ALU operand C

  ///////////////////////////////////////////////////////////////////
  // BIT MANIPULATION AND VECTOR CONTROL (PULP)
  ///////////////////////////////////////////////////////////////////
  logic [0:0] bmask_a_mux;            // Bit mask A multiplexer
  logic [1:0] bmask_b_mux;            // Bit mask B multiplexer
  logic       alu_bmask_a_mux_sel;    // ALU bit mask A select
  logic       alu_bmask_b_mux_sel;    // ALU bit mask B select
  logic [0:0] mult_imm_mux;           // Multiplier immediate select

  logic [4:0] bmask_a_id_imm;   // Bit mask A immediate value
  logic [4:0] bmask_b_id_imm;   // Bit mask B immediate value
  logic [4:0] bmask_a_id;       // Final bit mask A
  logic [4:0] bmask_b_id;       // Final bit mask B
  logic [1:0] imm_vec_ext_id;   // Vector extension immediate
  logic [4:0] mult_imm_id;      // Multiplier immediate

  logic       alu_vec;                 // Vector/SIMD operation enable
  logic [1:0] alu_vec_mode;            // Vector mode (8-bit, 16-bit)
  logic       scalar_replication;      // Replicate scalar to vector lanes
  logic       scalar_replication_c;    // Replicate scalar C to vector lanes

  ///////////////////////////////////////////////////////////////////
  // HAZARD DETECTION SIGNALS
  ///////////////////////////////////////////////////////////////////
  // EX stage forwarding detection
  logic reg_d_ex_is_reg_a_id;   // EX destination matches rs1
  logic reg_d_ex_is_reg_b_id;   // EX destination matches rs2
  logic reg_d_ex_is_reg_c_id;   // EX destination matches rs3

  // WB stage forwarding detection
  logic reg_d_wb_is_reg_a_id;   // WB destination matches rs1
  logic reg_d_wb_is_reg_b_id;   // WB destination matches rs2
  logic reg_d_wb_is_reg_c_id;   // WB destination matches rs3

  // ALU forwarding detection
  logic reg_d_alu_is_reg_a_id;  // ALU destination matches rs1
  logic reg_d_alu_is_reg_b_id;  // ALU destination matches rs2
  logic reg_d_alu_is_reg_c_id;  // ALU destination matches rs3

  ///////////////////////////////////////////////////////////////////
  // PULP EXTENSION FLAGS
  ///////////////////////////////////////////////////////////////////
  logic is_clpx;    // Complex number operation (PULP extension)
  logic is_subrot;  // Sub-rotation operation (PULP extension)

  ///////////////////////////////////////////////////////////////////
  // EXCEPTION RETURN SIGNALS
  ///////////////////////////////////////////////////////////////////
  logic mret_dec;  // MRET decoded (return from M-mode)
  logic uret_dec;  // URET decoded (return from U-mode)
  logic dret_dec;  // DRET decoded (return from Debug mode)

  ///////////////////////////////////////////////////////////////////
  // PERFORMANCE COUNTER SIGNALS
  ///////////////////////////////////////////////////////////////////
  logic id_valid_q;  // ID stage valid (registered for performance counting)
  logic minstret;            // Instruction retired (for minstret CSR)
  logic perf_pipeline_stall; // Pipeline stall indicator for performance counters

  ///////////////////////////////////////////////////////////////////
  // INSTRUCTION REGISTER
  ///////////////////////////////////////////////////////////////////
  // Assign incoming instruction to internal register
  assign instr = instr_rdata_i;

  ///////////////////////////////////////////////////////////////////
  // IMMEDIATE EXTRACTION AND SIGN EXTENSION
  ///////////////////////////////////////////////////////////////////
  // Extract and sign-extend immediate values for all RISC-V instruction formats
  
  // I-type immediate (12-bit signed): used for ADDI, SLTI, loads, JALR, etc.
  assign imm_i_type = {{20{instr[31]}}, instr[31:20]};
  
  // I-type immediate (zero-extended): used for shift amounts (SLLI, SRLI, SRAI)
  assign imm_iz_type = {20'b0, instr[31:20]};
  
  // S-type immediate (12-bit signed): used for stores (SW, SH, SB)
  assign imm_s_type = {{20{instr[31]}}, instr[31:25], instr[11:7]};
  
  // SB-type immediate (13-bit signed): used for branches (BEQ, BNE, BLT, etc.)
  // Note: LSB always 0 (2-byte aligned), so represents [-4096, +4094]
  assign imm_sb_type = {{19{instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0};
  
  // U-type immediate (20-bit upper): used for LUI, AUIPC
  assign imm_u_type = {instr[31:12], 12'b0};
  
  // UJ-type immediate (21-bit signed): used for JAL
  // Note: LSB always 0 (2-byte aligned), so represents [-1MB, +1MB]
  assign imm_uj_type = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};

  // Z-type immediate (zero-extended): used for CSR manipulation (CSRRWI, CSRRSI, CSRRCI)
  // Uses rs1 field as 5-bit unsigned immediate
  assign imm_z_type = {27'b0, instr[REG_S1_MSB:REG_S1_LSB]};

  ///////////////////////////////////////////////////////////////////
  // PULP EXTENSION IMMEDIATE FORMATS
  ///////////////////////////////////////////////////////////////////
  // S2-type immediate: PULP extension (5-bit unsigned from rs2 field)
  assign imm_s2_type = {27'b0, instr[24:20]};
  
  // BI-type immediate: PULP extension (5-bit signed)
  assign imm_bi_type = {{27{instr[24]}}, instr[24:20]};
  
  // S3-type immediate: PULP extension (5-bit unsigned from funct5 field)
  assign imm_s3_type = {27'b0, instr[29:25]};
  
  // VS-type immediate: PULP vector extension (6-bit signed)
  assign imm_vs_type = {{26{instr[24]}}, instr[24:20], instr[25]};
  
  // VU-type immediate: PULP vector extension (6-bit unsigned)
  assign imm_vu_type = {26'b0, instr[24:20], instr[25]};

  // Shuffle byte immediate: expands bits into byte-wise shuffle control
  // Format matches rS2 for shuffle operations, spreads bits across bytes
  assign imm_shuffleb_type = {
    6'b0, instr[28:27], 6'b0, instr[24:23], 6'b0, instr[22:21], 6'b0, instr[20], instr[25]
  };
  
  // Shuffle halfword immediate: similar to shuffleb but for 16-bit elements
  assign imm_shuffleh_type = {15'h0, instr[20], 15'h0, instr[25]};

  // Clip immediate: creates a bitmask for clip/clipu operations
  // Computes (1 << imm) - 1 to create mask with lower bits set
  // Example: imm=5 -> 0x0000001F (mask for 5 bits)
  assign imm_clip_type = (32'h1 << instr[24:20]) - 1;

  ///////////////////////////////////////////////////////////////////
  // SOURCE REGISTER ADDRESS EXTRACTION
  ///////////////////////////////////////////////////////////////////
  // Extract source register addresses from instruction fields
  // Bit 5 (regfile_fp_x) indicates FP register when ZFINX=0
  
  // rs1 address (source register 1)
  assign regfile_addr_ra_id = {regfile_fp_a, instr[REG_S1_MSB:REG_S1_LSB]};
  
  // rs2 address (source register 2)
  assign regfile_addr_rb_id = {regfile_fp_b, instr[REG_S2_MSB:REG_S2_LSB]};

  // Register C address multiplexer
  // Selects between different instruction fields for rs3 based on instruction type
  always_comb begin
    unique case (regc_mux)
      REGC_ZERO: regfile_addr_rc_id = '0;                                     // No register C
      REGC_RD:   regfile_addr_rc_id = {regfile_fp_c, instr[REG_D_MSB:REG_D_LSB]};   // Use rd field (for stores)
      REGC_S1:   regfile_addr_rc_id = {regfile_fp_c, instr[REG_S1_MSB:REG_S1_LSB]}; // Use rs1 field
      REGC_S4:   regfile_addr_rc_id = {regfile_fp_c, instr[REG_S4_MSB:REG_S4_LSB]}; // Use rs4 field (PULP)
    endcase
  end

  ///////////////////////////////////////////////////////////////////
  // DESTINATION REGISTER ADDRESS EXTRACTION
  ///////////////////////////////////////////////////////////////////
  // rd address (destination register)
  // Bit 5 (regfile_fp_d) indicates FP register when ZFINX=0
  assign regfile_waddr_id = {regfile_fp_d, instr[REG_D_MSB:REG_D_LSB]};

  // Second register write address for special operations
  // Used for post-increment addressing (PULP) and multiplier accumulate
  // Selects between rd (normal) or rs1 (for post-increment where rs1 is updated)
  assign regfile_alu_waddr_id = regfile_alu_waddr_mux_sel ? regfile_waddr_id : regfile_addr_ra_id;

  ///////////////////////////////////////////////////////////////////
  // FORWARDING HAZARD DETECTION
  ///////////////////////////////////////////////////////////////////
  // Detect Read-After-Write (RAW) hazards by comparing destination registers
  // in EX and WB stages with source registers in ID stage
  // Note: x0 is always 0 and doesn't need forwarding (hence != '0 check)
  
  // EX stage hazard detection (1-cycle penalty if not forwarded)
  assign reg_d_ex_is_reg_a_id  = (regfile_waddr_ex_o     == regfile_addr_ra_id) && (rega_used_dec == 1'b1) && (regfile_addr_ra_id != '0);
  assign reg_d_ex_is_reg_b_id  = (regfile_waddr_ex_o     == regfile_addr_rb_id) && (regb_used_dec == 1'b1) && (regfile_addr_rb_id != '0);
  assign reg_d_ex_is_reg_c_id  = (regfile_waddr_ex_o     == regfile_addr_rc_id) && (regc_used_dec == 1'b1) && (regfile_addr_rc_id != '0);
  
  // WB stage hazard detection (2-cycle penalty if not forwarded)
  assign reg_d_wb_is_reg_a_id  = (regfile_waddr_wb_i     == regfile_addr_ra_id) && (rega_used_dec == 1'b1) && (regfile_addr_ra_id != '0);
  assign reg_d_wb_is_reg_b_id  = (regfile_waddr_wb_i     == regfile_addr_rb_id) && (regb_used_dec == 1'b1) && (regfile_addr_rb_id != '0);
  assign reg_d_wb_is_reg_c_id  = (regfile_waddr_wb_i     == regfile_addr_rc_id) && (regc_used_dec == 1'b1) && (regfile_addr_rc_id != '0);
  
  // ALU forwarding path hazard detection (from EX stage ALU result)
  assign reg_d_alu_is_reg_a_id = (regfile_alu_waddr_fw_i == regfile_addr_ra_id) && (rega_used_dec == 1'b1) && (regfile_addr_ra_id != '0);
  assign reg_d_alu_is_reg_b_id = (regfile_alu_waddr_fw_i == regfile_addr_rb_id) && (regb_used_dec == 1'b1) && (regfile_addr_rb_id != '0);
  assign reg_d_alu_is_reg_c_id = (regfile_alu_waddr_fw_i == regfile_addr_rc_id) && (regc_used_dec == 1'b1) && (regfile_addr_rc_id != '0);

  ///////////////////////////////////////////////////////////////////
  // PIPELINE CONTROL SIGNALS
  ///////////////////////////////////////////////////////////////////
  // Clear instruction valid signal when:
  // - ID stage is ready (instruction completes)
  // - Pipeline is halted (exception/interrupt)
  // - Branch is taken in EX (flush pipeline)
  assign clear_instr_valid_o = id_ready_o | halt_id | branch_taken_ex;

  // Branch taken when branch instruction in EX and condition is true
  assign branch_taken_ex = branch_in_ex_o && branch_decision_i;

  // Multiplier enable if either integer multiply or dot product active
  assign mult_en = mult_int_en | mult_dot_en;

  ///////////////////////////////////////////////////////////////////
  //      _                         _____                    _
  //     | |_   _ _ __ ___  _ __   |_   _|_ _ _ __ __ _  ___| |_
  //  _  | | | | | '_ ` _ \| '_ \    | |/ _` | '__/ _` |/ _ \ __|
  // | |_| | |_| | | | | | | |_) |   | | (_| | | | (_| |  __/ |_
  //  \___/ \__,_|_| |_| |_| .__/    |_|\__,_|_|  \__, |\___|\__|
  //                       |_|                    |___/
  ///////////////////////////////////////////////////////////////////
  // JUMP TARGET CALCULATION
  ///////////////////////////////////////////////////////////////////
  // Calculate target address for control transfer instructions
  // - JAL: PC + imm_uj (21-bit signed offset)
  // - Branch: PC + imm_sb (13-bit signed offset)
  // - JALR: rs1 + imm_i (12-bit signed offset)
  //         Note: Cannot forward rs1 due to timing - path too long
  
  always_comb begin : jump_target_mux
    unique case (ctrl_transfer_target_mux_sel)
      JT_JAL:  jump_target = pc_id_i + imm_uj_type;  // JAL: PC-relative
      JT_COND: jump_target = pc_id_i + imm_sb_type;  // Branch: PC-relative

      // JALR: Register-relative (no forwarding to meet timing)
      JT_JALR: jump_target = regfile_data_ra_id + imm_i_type;
      default: jump_target = regfile_data_ra_id + imm_i_type;
    endcase
  end

  // Output jump target to controller
  assign jump_target_o = jump_target;


  ///////////////////////////////////////////////////////////////////
  //   ___                                 _      _
  //  / _ \ _ __   ___ _ __ __ _ _ __   __| |    / \
  // | | | | '_ \ / _ \ '__/ _` | '_ \ / _` |   / _ \
  // | |_| | |_) |  __/ | | (_| | | | | (_| |  / ___ \
  //  \___/| .__/ \___|_|  \__,_|_| |_|\__,_| /_/   \_\
  //       |_|
  ///////////////////////////////////////////////////////////////////
  // OPERAND A SELECTION
  ///////////////////////////////////////////////////////////////////
  // Operand A can come from:
  // - Register A (rs1) with forwarding
  // - Register B (rs2) with forwarding  
  // - Register C (rs3) with forwarding
  // - Current PC (for AUIPC, branches)
  // - Immediate value (for CSR instructions)

  always_comb begin : alu_operand_a_mux
    case (alu_op_a_mux_sel)
      OP_A_REGA_OR_FWD: alu_operand_a = operand_a_fw_id;  // Normal case: rs1
      OP_A_REGB_OR_FWD: alu_operand_a = operand_b_fw_id;  // Use rs2 as operand A
      OP_A_REGC_OR_FWD: alu_operand_a = operand_c_fw_id;  // Use rs3 as operand A (PULP)
      OP_A_CURRPC:      alu_operand_a = pc_id_i;          // PC (for AUIPC, branch addresses)
      OP_A_IMM:         alu_operand_a = imm_a;            // Immediate (for CSR)
      default:          alu_operand_a = operand_a_fw_id;
    endcase
    ;  // case (alu_op_a_mux_sel)
  end

  // Immediate A multiplexer
  // Selects immediate value when OP_A_IMM is used
  always_comb begin : immediate_a_mux
    unique case (imm_a_mux_sel)
      IMMA_Z:    imm_a = imm_z_type;  // Zero-extended immediate (CSR uimm)
      IMMA_ZERO: imm_a = '0;          // Zero
    endcase
  end

  // Operand A forwarding multiplexer
  // Handles data hazards by forwarding from EX or WB stages
  // Priority: EX > WB > Register File (most recent data)
  always_comb begin : operand_a_fw_mux
    case (operand_a_fw_mux_sel)
      SEL_FW_EX:   operand_a_fw_id = regfile_alu_wdata_fw_i;  // Forward from EX stage
      SEL_FW_WB:   operand_a_fw_id = regfile_wdata_wb_i;      // Forward from WB stage
      SEL_REGFILE: operand_a_fw_id = regfile_data_ra_id;      // No forwarding needed
      default:     operand_a_fw_id = regfile_data_ra_id;
    endcase
    ;  // case (operand_a_fw_mux_sel)
  end

  ///////////////////////////////////////////////////////////////////
  //   ___                                 _   ____
  //  / _ \ _ __   ___ _ __ __ _ _ __   __| | | __ )
  // | | | | '_ \ / _ \ '__/ _` | '_ \ / _` | |  _ \
  // | |_| | |_) |  __/ | | (_| | | | | (_| | | |_) |
  //  \___/| .__/ \___|_|  \__,_|_| |_|\__,_| |____/
  //       |_|
  ///////////////////////////////////////////////////////////////////
  // OPERAND B SELECTION
  ///////////////////////////////////////////////////////////////////
  // Operand B can come from:
  // - Immediate values (all RISC-V formats + PULP extensions)
  // - Register values with forwarding
  // - Special values (PC increment for return address)

  // Immediate B multiplexer
  // Supports all RISC-V immediate formats plus PULP extensions
  always_comb begin : immediate_b_mux
    unique case (imm_b_mux_sel)
      IMMB_I:      imm_b = imm_i_type;                      // I-type (ADDI, loads, etc.)
      IMMB_S:      imm_b = imm_s_type;                      // S-type (stores)
      IMMB_U:      imm_b = imm_u_type;                      // U-type (LUI, AUIPC)
      IMMB_PCINCR: imm_b = is_compressed_i ? 32'h2 : 32'h4; // PC increment (2 for RVC, 4 for RV32)
      IMMB_S2:     imm_b = imm_s2_type;                     // PULP S2-type
      IMMB_BI:     imm_b = imm_bi_type;                     // PULP BI-type
      IMMB_S3:     imm_b = imm_s3_type;                     // PULP S3-type
      IMMB_VS:     imm_b = imm_vs_type;                     // PULP vector signed
      IMMB_VU:     imm_b = imm_vu_type;                     // PULP vector unsigned
      IMMB_SHUF:   imm_b = imm_shuffle_type;                // PULP shuffle
      IMMB_CLIP:   imm_b = {1'b0, imm_clip_type[31:1]};     // PULP clip (shift right by 1)
      default:     imm_b = imm_i_type;
    endcase
  end

  // ALU Operand B multiplexer
  // Selects between registers, immediates, and special values
  always_comb begin : alu_operand_b_mux
    case (alu_op_b_mux_sel)
      OP_B_REGA_OR_FWD: operand_b = operand_a_fw_id;           // Use rs1
      OP_B_REGB_OR_FWD: operand_b = operand_b_fw_id;           // Use rs2 (normal)
      OP_B_REGC_OR_FWD: operand_b = operand_c_fw_id;           // Use rs3 (PULP)
      OP_B_IMM:         operand_b = imm_b;                     // Immediate value
      OP_B_BMASK:       operand_b = $unsigned(operand_b_fw_id[4:0]); // Bit mask (lower 5 bits)
      default:          operand_b = operand_b_fw_id;
    endcase  // case (alu_op_b_mux_sel)
  end

  // Scalar replication for SIMD operations (PULP extension)
  // Replicates scalar value across vector lanes:
  // - VEC_MODE8: 4 copies of byte [7:0] -> {byte, byte, byte, byte}
  // - VEC_MODE16: 2 copies of halfword [15:0] -> {half, half}
  always_comb begin
    if (alu_vec_mode == VEC_MODE8) begin
      operand_b_vec    = {4{operand_b[7:0]}};      // Replicate byte 4 times
      imm_shuffle_type = imm_shuffleb_type;        // Use byte shuffle immediate
    end else begin
      operand_b_vec    = {2{operand_b[15:0]}};     // Replicate halfword 2 times
      imm_shuffle_type = imm_shuffleh_type;        // Use halfword shuffle immediate
    end
  end

  // Select between normal and scalar-replicated operand B
  assign alu_operand_b = (scalar_replication == 1'b1) ? operand_b_vec : operand_b;

  // Operand B forwarding multiplexer
  // Handles data hazards by forwarding from EX or WB stages
  always_comb begin : operand_b_fw_mux
    case (operand_b_fw_mux_sel)
      SEL_FW_EX:   operand_b_fw_id = regfile_alu_wdata_fw_i;  // Forward from EX stage
      SEL_FW_WB:   operand_b_fw_id = regfile_wdata_wb_i;      // Forward from WB stage
      SEL_REGFILE: operand_b_fw_id = regfile_data_rb_id;      // No forwarding needed
      default:     operand_b_fw_id = regfile_data_rb_id;
    endcase
    ;  // case (operand_b_fw_mux_sel)
  end


  ///////////////////////////////////////////////////////////////////
  //   ___                                 _    ____
  //  / _ \ _ __   ___ _ __ __ _ _ __   __| |  / ___|
  // | | | | '_ \ / _ \ '__/ _` | '_ \ / _` | | |
  // | |_| | |_) |  __/ | | (_| | | | | (_| | | |___
  //  \___/| .__/ \___|_|  \__,_|_| |_|\__,_|  \____|
  //       |_|
  ///////////////////////////////////////////////////////////////////
  // OPERAND C SELECTION
  ///////////////////////////////////////////////////////////////////
  // Operand C is primarily used for:
  // - Three-operand instructions (PULP extensions: MAC, dot product)
  // - Store data (rs2 value to be stored)
  // - Special operations requiring third operand

  // ALU Operand C multiplexer
  always_comb begin : alu_operand_c_mux
    case (alu_op_c_mux_sel)
      OP_C_REGC_OR_FWD: operand_c = operand_c_fw_id;  // Use rs3/rs2 with forwarding
      OP_C_REGB_OR_FWD: operand_c = operand_b_fw_id;  // Use rs2 with forwarding
      OP_C_JT:          operand_c = jump_target;      // Jump target (for special ops)
      default:          operand_c = operand_c_fw_id;
    endcase  // case (alu_op_c_mux_sel)
  end

  // Scalar replication for operand C in SIMD operations (PULP extension)
  // Similar to operand B: replicate scalar value across vector lanes
  always_comb begin
    if (alu_vec_mode == VEC_MODE8) begin
      operand_c_vec = {4{operand_c[7:0]}};      // Replicate byte 4 times
    end else begin
      operand_c_vec = {2{operand_c[15:0]}};     // Replicate halfword 2 times
    end
  end

  // Select between normal and scalar-replicated operand C
  assign alu_operand_c = (scalar_replication_c == 1'b1) ? operand_c_vec : operand_c;

  // Operand C forwarding multiplexer
  // Handles data hazards by forwarding from EX or WB stages
  always_comb begin : operand_c_fw_mux
    case (operand_c_fw_mux_sel)
      SEL_FW_EX:   operand_c_fw_id = regfile_alu_wdata_fw_i;  // Forward from EX stage
      SEL_FW_WB:   operand_c_fw_id = regfile_wdata_wb_i;      // Forward from WB stage
      SEL_REGFILE: operand_c_fw_id = regfile_data_rc_id;      // No forwarding needed
      default:     operand_c_fw_id = regfile_data_rc_id;
    endcase
    ;  // case (operand_c_fw_mux_sel)
  end


  ///////////////////////////////////////////////////////////////////
  //  ___                              _ _       _              ___ ____
  // |_ _|_ __ ___  _ __ ___   ___  __| (_) __ _| |_ ___  ___  |_ _|  _ \
  //  | || '_ ` _ \| '_ ` _ \ / _ \/ _` | |/ _` | __/ _ \/ __|  | || | | |
  //  | || | | | | | | | | | |  __/ (_| | | (_| | ||  __/\__ \  | || |_| |
  // |___|_| |_| |_|_| |_| |_|\___|\__,_|_|\__,_|\__\___||___/ |___|____/
  ///////////////////////////////////////////////////////////////////
  // BIT MANIPULATION IMMEDIATES (PULP Extension)
  ///////////////////////////////////////////////////////////////////
  // Bit masks for bit manipulation instructions (extract, insert, etc.)
  // Support both immediate and register-based bit positions

  // Bit mask A immediate multiplexer
  always_comb begin
    unique case (bmask_a_mux)
      BMASK_A_ZERO: bmask_a_id_imm = '0;            // No mask
      BMASK_A_S3:   bmask_a_id_imm = imm_s3_type[4:0]; // 5-bit immediate from S3 field
    endcase
  end
  
  // Bit mask B immediate multiplexer
  always_comb begin
    unique case (bmask_b_mux)
      BMASK_B_ZERO: bmask_b_id_imm = '0;            // No mask
      BMASK_B_ONE:  bmask_b_id_imm = 5'd1;          // Mask of 1
      BMASK_B_S2:   bmask_b_id_imm = imm_s2_type[4:0]; // 5-bit immediate from S2 field
      BMASK_B_S3:   bmask_b_id_imm = imm_s3_type[4:0]; // 5-bit immediate from S3 field
    endcase
  end

  // Final bit mask A selection (immediate vs register-based)
  always_comb begin
    unique case (alu_bmask_a_mux_sel)
      BMASK_A_IMM: bmask_a_id = bmask_a_id_imm;      // Use immediate value
      BMASK_A_REG: bmask_a_id = operand_b_fw_id[9:5]; // Extract from register bits [9:5]
    endcase
  end
  
  // Final bit mask B selection (immediate vs register-based)
  always_comb begin
    unique case (alu_bmask_b_mux_sel)
      BMASK_B_IMM: bmask_b_id = bmask_b_id_imm;      // Use immediate value
      BMASK_B_REG: bmask_b_id = operand_b_fw_id[4:0]; // Extract from register bits [4:0]
    endcase
  end

  // Vector extension immediate selection (PULP)
  generate
    if (!COREV_PULP) begin
      assign imm_vec_ext_id = imm_vu_type[1:0];  // Always use VU-type for non-PULP
    end else begin
      assign imm_vec_ext_id = (alu_vec) ? imm_vu_type[1:0] : 2'b0; // Conditional on vector mode
    end
  endgenerate

  // Multiplier immediate selection
  always_comb begin
    unique case (mult_imm_mux)
      MIMM_ZERO: mult_imm_id = '0;                // No immediate
      MIMM_S3:   mult_imm_id = imm_s3_type[4:0];  // 5-bit immediate from S3 field
    endcase
  end

  ///////////////////////////////////////////////////////////////////
  // APU (AUXILIARY PROCESSING UNIT) OPERAND ASSIGNMENT
  ///////////////////////////////////////////////////////////////////
  // Maps CPU operands to APU/FPU interface
  // Handles dependency tracking for APU instructions
  generate
    if (APU == 1) begin : gen_apu

      if (APU_NARGS_CPU >= 1) assign apu_operands[0] = alu_operand_a;
      if (APU_NARGS_CPU >= 2) assign apu_operands[1] = alu_operand_b;
      if (APU_NARGS_CPU >= 3) assign apu_operands[2] = alu_operand_c;

      // write reg
      assign apu_waddr = regfile_alu_waddr_id;

      // flags
      assign apu_flags = (FPU == 1) ? {fpu_int_fmt, fpu_src_fmt, fpu_dst_fmt, fp_rnd_mode} : '0;

      // dependency checks
      always_comb begin
        unique case (alu_op_a_mux_sel)
          OP_A_CURRPC: begin
            if (ctrl_transfer_target_mux_sel == JT_JALR) begin
              apu_read_regs[0]       = regfile_addr_ra_id;
              apu_read_regs_valid[0] = 1'b1;
            end else begin
              apu_read_regs[0]       = regfile_addr_ra_id;
              apu_read_regs_valid[0] = 1'b0;
            end
          end  // OP_A_CURRPC:
          OP_A_REGA_OR_FWD: begin
            apu_read_regs[0]       = regfile_addr_ra_id;
            apu_read_regs_valid[0] = 1'b1;
          end  // OP_A_REGA_OR_FWD:
          OP_A_REGB_OR_FWD, OP_A_REGC_OR_FWD: begin
            apu_read_regs[0]       = regfile_addr_rb_id;
            apu_read_regs_valid[0] = 1'b1;
          end
          default: begin
            apu_read_regs[0]       = regfile_addr_ra_id;
            apu_read_regs_valid[0] = 1'b0;
          end
        endcase
      end

      always_comb begin
        unique case (alu_op_b_mux_sel)
          OP_B_REGA_OR_FWD: begin
            apu_read_regs[1]       = regfile_addr_ra_id;
            apu_read_regs_valid[1] = 1'b1;
          end
          OP_B_REGB_OR_FWD, OP_B_BMASK: begin
            apu_read_regs[1]       = regfile_addr_rb_id;
            apu_read_regs_valid[1] = 1'b1;
          end
          OP_B_REGC_OR_FWD: begin
            apu_read_regs[1]       = regfile_addr_rc_id;
            apu_read_regs_valid[1] = 1'b1;
          end
          OP_B_IMM: begin
            if (alu_bmask_b_mux_sel == BMASK_B_REG) begin
              apu_read_regs[1]       = regfile_addr_rb_id;
              apu_read_regs_valid[1] = 1'b1;
            end else begin
              apu_read_regs[1]       = regfile_addr_rb_id;
              apu_read_regs_valid[1] = 1'b0;
            end
          end
          default: begin
            apu_read_regs[1]       = regfile_addr_rb_id;
            apu_read_regs_valid[1] = 1'b0;
          end
        endcase
      end

      always_comb begin
        unique case (alu_op_c_mux_sel)
          OP_C_REGB_OR_FWD: begin
            apu_read_regs[2]       = regfile_addr_rb_id;
            apu_read_regs_valid[2] = 1'b1;
          end
          OP_C_REGC_OR_FWD: begin
            if ((alu_op_a_mux_sel != OP_A_REGC_OR_FWD) && (ctrl_transfer_target_mux_sel != JT_JALR) &&
                !((alu_op_b_mux_sel == OP_B_IMM) && (alu_bmask_b_mux_sel == BMASK_B_REG)) &&
                !(alu_op_b_mux_sel == OP_B_BMASK)) begin
              apu_read_regs[2]       = regfile_addr_rc_id;
              apu_read_regs_valid[2] = 1'b1;
            end else begin
              apu_read_regs[2]       = regfile_addr_rc_id;
              apu_read_regs_valid[2] = 1'b0;
            end
          end
          default: begin
            apu_read_regs[2]       = regfile_addr_rc_id;
            apu_read_regs_valid[2] = 1'b0;
          end
        endcase
      end

      assign apu_write_regs[0]       = regfile_alu_waddr_id;
      assign apu_write_regs_valid[0] = regfile_alu_we_id;

      assign apu_write_regs[1]       = regfile_waddr_id;
      assign apu_write_regs_valid[1] = regfile_we_id;

      assign apu_read_regs_o         = apu_read_regs;
      assign apu_read_regs_valid_o   = apu_read_regs_valid;

      assign apu_write_regs_o        = apu_write_regs;
      assign apu_write_regs_valid_o  = apu_write_regs_valid;
    end else begin : gen_no_apu
      for (genvar i = 0; i < APU_NARGS_CPU; i++) begin : gen_apu_tie_off
        assign apu_operands[i] = '0;
      end

      assign apu_read_regs          = '0;
      assign apu_read_regs_valid    = '0;
      assign apu_write_regs         = '0;
      assign apu_write_regs_valid   = '0;
      assign apu_waddr              = '0;
      assign apu_flags              = '0;
      assign apu_write_regs_o       = '0;
      assign apu_read_regs_o        = '0;
      assign apu_write_regs_valid_o = '0;
      assign apu_read_regs_valid_o  = '0;
    end
  endgenerate

  assign apu_perf_dep_o = apu_stall;
  
  // APU/CSR stall logic
  // Stall when accessing CSR while a multicycle APU instruction is in progress
  // This prevents CSR operations from interfering with APU state
  assign csr_apu_stall  = (csr_access & (apu_en_ex_o & (apu_lat_ex_o[1] == 1'b1) | apu_busy_i));

  ///////////////////////////////////////////////////////////////////
  //  ____  _____ ____ ___ ____ _____ _____ ____  ____
  // |  _ \| ____/ ___|_ _/ ___|_   _| ____|  _ \/ ___|
  // | |_) |  _|| |  _ | |\___ \ | | |  _| | |_) \___ \
  // |  _ <| |__| |_| || | ___) || | | |___|  _ < ___) |
  // |_| \_\_____\____|___|____/ |_| |_____|_| \_\____/
  ///////////////////////////////////////////////////////////////////
  // REGISTER FILE INSTANTIATION
  ///////////////////////////////////////////////////////////////////
  // 31 general-purpose registers (x1-x31), x0 hardwired to 0
  // - 3 read ports (A, B, C) for up to 3 source operands
  // - 2 write ports (A from WB stage, B from EX stage for ALU forwarding)
  // - Supports FPU register file when FPU=1 and ZFINX=0
  // - Can be implemented as flip-flops or latches (see register_file module)
  
  cv32e40p_register_file #(
      .ADDR_WIDTH(6),
      .DATA_WIDTH(32),
      .FPU       (FPU),
      .ZFINX     (ZFINX)
  ) register_file_i (
      .clk  (clk),
      .rst_n(rst_n),

      .scan_cg_en_i(scan_cg_en_i),

      // Read port a
      .raddr_a_i(regfile_addr_ra_id),
      .rdata_a_o(regfile_data_ra_id),

      // Read port b
      .raddr_b_i(regfile_addr_rb_id),
      .rdata_b_o(regfile_data_rb_id),

      // Read port c
      .raddr_c_i(regfile_addr_rc_id),
      .rdata_c_o(regfile_data_rc_id),

      // Write port a
      .waddr_a_i(regfile_waddr_wb_i),
      .wdata_a_i(regfile_wdata_wb_i),
      .we_a_i   (regfile_we_wb_power_i),

      // Write port b
      .waddr_b_i(regfile_alu_waddr_fw_i),
      .wdata_b_i(regfile_alu_wdata_fw_i),
      .we_b_i   (regfile_alu_we_fw_power_i)
  );

  ///////////////////////////////////////////////////////////////////
  //  ____  _____ ____ ___  ____  _____ ____
  // |  _ \| ____/ ___/ _ \|  _ \| ____|  _ \
  // | | | |  _|| |  | | | | | | |  _| | |_) |
  // | |_| | |__| |__| |_| | |_| | |___|  _ <
  // |____/|_____\____\___/|____/|_____|_| \_\
  ///////////////////////////////////////////////////////////////////
  // INSTRUCTION DECODER INSTANTIATION
  ///////////////////////////////////////////////////////////////////
  // Main instruction decoder - decodes all RV32IMC instructions plus PULP extensions
  // Generates all control signals for:
  // - ALU operations (arithmetic, logical, comparison, bit manipulation)
  // - Multiplier operations (MUL, MULH, MULHSU, MULHU, dot product, MAC)
  // - Load/store operations (LW, LH, LB, SW, SH, SB with sign extension)
  // - Branch/jump operations (BEQ, BNE, BLT, BGE, JAL, JALR)
  // - CSR operations (CSRRW, CSRRS, CSRRC and immediate variants)
  // - FPU/APU operations (floating-point arithmetic when FPU=1)
  // - PULP extensions (hardware loops, post-increment, vector/SIMD, etc.)
  // - Atomic operations (A extension: LR, SC, AMO*)
  // - Exception detection (illegal instructions, ECALL, EBREAK)
  
  cv32e40p_decoder #(
      .COREV_PULP      (COREV_PULP),
      .COREV_CLUSTER   (COREV_CLUSTER),
      .A_EXTENSION     (A_EXTENSION),
      .FPU             (FPU),
      .FPU_ADDMUL_LAT  (FPU_ADDMUL_LAT),
      .FPU_OTHERS_LAT  (FPU_OTHERS_LAT),
      .ZFINX           (ZFINX),
      .PULP_SECURE     (PULP_SECURE),
      .USE_PMP         (USE_PMP),
      .APU_WOP_CPU     (APU_WOP_CPU),
      .DEBUG_TRIGGER_EN(DEBUG_TRIGGER_EN)
  ) decoder_i (
      // controller related signals
      .deassert_we_i(deassert_we),

      .illegal_insn_o(illegal_insn_dec),
      .ebrk_insn_o   (ebrk_insn_dec),

      .mret_insn_o(mret_insn_dec),
      .uret_insn_o(uret_insn_dec),
      .dret_insn_o(dret_insn_dec),

      .mret_dec_o(mret_dec),
      .uret_dec_o(uret_dec),
      .dret_dec_o(dret_dec),

      .ecall_insn_o(ecall_insn_dec),
      .wfi_o       (wfi_insn_dec),

      .fencei_insn_o(fencei_insn_dec),

      .rega_used_o(rega_used_dec),
      .regb_used_o(regb_used_dec),
      .regc_used_o(regc_used_dec),

      .reg_fp_a_o(regfile_fp_a),
      .reg_fp_b_o(regfile_fp_b),
      .reg_fp_c_o(regfile_fp_c),
      .reg_fp_d_o(regfile_fp_d),

      .bmask_a_mux_o        (bmask_a_mux),
      .bmask_b_mux_o        (bmask_b_mux),
      .alu_bmask_a_mux_sel_o(alu_bmask_a_mux_sel),
      .alu_bmask_b_mux_sel_o(alu_bmask_b_mux_sel),

      // from IF/ID pipeline
      .instr_rdata_i   (instr),
      .illegal_c_insn_i(illegal_c_insn_i),

      // ALU signals
      .alu_en_o              (alu_en),
      .alu_operator_o        (alu_operator),
      .alu_op_a_mux_sel_o    (alu_op_a_mux_sel),
      .alu_op_b_mux_sel_o    (alu_op_b_mux_sel),
      .alu_op_c_mux_sel_o    (alu_op_c_mux_sel),
      .alu_vec_o             (alu_vec),
      .alu_vec_mode_o        (alu_vec_mode),
      .scalar_replication_o  (scalar_replication),
      .scalar_replication_c_o(scalar_replication_c),
      .imm_a_mux_sel_o       (imm_a_mux_sel),
      .imm_b_mux_sel_o       (imm_b_mux_sel),
      .regc_mux_o            (regc_mux),
      .is_clpx_o             (is_clpx),
      .is_subrot_o           (is_subrot),

      // MUL signals
      .mult_operator_o   (mult_operator),
      .mult_int_en_o     (mult_int_en),
      .mult_sel_subword_o(mult_sel_subword),
      .mult_signed_mode_o(mult_signed_mode),
      .mult_imm_mux_o    (mult_imm_mux),
      .mult_dot_en_o     (mult_dot_en),
      .mult_dot_signed_o (mult_dot_signed),

      // FPU / APU signals
      .fs_off_i     (fs_off_i),
      .frm_i        (frm_i),
      .fpu_src_fmt_o(fpu_src_fmt),
      .fpu_dst_fmt_o(fpu_dst_fmt),
      .fpu_int_fmt_o(fpu_int_fmt),
      .apu_en_o     (apu_en),
      .apu_op_o     (apu_op),
      .apu_lat_o    (apu_lat),
      .fp_rnd_mode_o(fp_rnd_mode),

      // Register file control signals
      .regfile_mem_we_o       (regfile_we_id),
      .regfile_alu_we_o       (regfile_alu_we_id),
      .regfile_alu_we_dec_o   (regfile_alu_we_dec_id),
      .regfile_alu_waddr_sel_o(regfile_alu_waddr_mux_sel),

      // CSR control signals
      .csr_access_o      (csr_access),
      .csr_status_o      (csr_status),
      .csr_op_o          (csr_op),
      .current_priv_lvl_i(current_priv_lvl_i),

      // Data bus interface
      .data_req_o           (data_req_id),
      .data_we_o            (data_we_id),
      .prepost_useincr_o    (prepost_useincr),
      .data_type_o          (data_type_id),
      .data_sign_extension_o(data_sign_ext_id),
      .data_reg_offset_o    (data_reg_offset_id),
      .data_load_event_o    (data_load_event_id),

      // Atomic memory access
      .atop_o(atop_id),

      // hwloop signals
      .hwlp_we_o            (hwlp_we),
      .hwlp_target_mux_sel_o(hwlp_target_mux_sel),
      .hwlp_start_mux_sel_o (hwlp_start_mux_sel),
      .hwlp_cnt_mux_sel_o   (hwlp_cnt_mux_sel),

      // debug mode
      .debug_mode_i        (debug_mode_o),
      .debug_wfi_no_sleep_i(debug_wfi_no_sleep),

      // jump/branches
      .ctrl_transfer_insn_in_dec_o   (ctrl_transfer_insn_in_dec_o),
      .ctrl_transfer_insn_in_id_o    (ctrl_transfer_insn_in_id),
      .ctrl_transfer_target_mux_sel_o(ctrl_transfer_target_mux_sel),

      // HPM related control signals
      .mcounteren_i(mcounteren_i)

  );

  ///////////////////////////////////////////////////////////////////
  //    ____ ___  _   _ _____ ____   ___  _     _     _____ ____
  //   / ___/ _ \| \ | |_   _|  _ \ / _ \| |   | |   | ____|  _ \
  //  | |  | | | |  \| | | | | |_) | | | | |   | |   |  _| | |_) |
  //  | |__| |_| | |\  | | | |  _ <| |_| | |___| |___| |___|  _ <
  //   \____\___/|_| \_| |_| |_| \_\\___/|_____|_____|_____|_| \_\
  ///////////////////////////////////////////////////////////////////
  // PIPELINE CONTROLLER INSTANTIATION
  ///////////////////////////////////////////////////////////////////
  // Main pipeline controller - manages all pipeline control flow including:
  // - Exception and interrupt handling (M-mode, U-mode, Debug mode)
  // - Pipeline stalls and flushes (data hazards, multi-cycle operations)
  // - Data forwarding control (EX→ID, WB→ID forwarding paths)
  // - Hardware loop control (PULP extension: automatic loop management)
  // - Debug mode entry/exit (Debug Specification v0.13.2)
  // - PC control (jumps, branches, exceptions, interrupts, returns)
  // - CSR state management (save/restore on traps)
  // - Wake-up from sleep (WFI instruction)
  // - Load/store unit synchronization
  // - APU/FPU pipeline coordination
  
  cv32e40p_controller #(
      .COREV_CLUSTER(COREV_CLUSTER),
      .COREV_PULP   (COREV_PULP),
      .FPU          (FPU)
  ) controller_i (
      .clk          (clk),  // Gated clock
      .clk_ungated_i(clk_ungated_i),  // Ungated clock
      .rst_n        (rst_n),

      .fetch_enable_i   (fetch_enable_i),
      .ctrl_busy_o      (ctrl_busy_o),
      .is_decoding_o    (is_decoding_o),
      .is_fetch_failed_i(is_fetch_failed_i),

      // decoder related signals
      .deassert_we_o(deassert_we),

      .illegal_insn_i(illegal_insn_dec),
      .ecall_insn_i  (ecall_insn_dec),
      .mret_insn_i   (mret_insn_dec),
      .uret_insn_i   (uret_insn_dec),

      .dret_insn_i(dret_insn_dec),

      .mret_dec_i(mret_dec),
      .uret_dec_i(uret_dec),
      .dret_dec_i(dret_dec),


      .wfi_i        (wfi_insn_dec),
      .ebrk_insn_i  (ebrk_insn_dec),
      .fencei_insn_i(fencei_insn_dec),
      .csr_status_i (csr_status),

      .hwlp_mask_o(hwlp_mask),

      // from IF/ID pipeline
      .instr_valid_i(instr_valid_i),

      // from prefetcher
      .instr_req_o(instr_req_o),

      // to prefetcher
      .pc_set_o       (pc_set_o),
      .pc_mux_o       (pc_mux_o),
      .exc_pc_mux_o   (exc_pc_mux_o),
      .exc_cause_o    (exc_cause_o),
      .trap_addr_mux_o(trap_addr_mux_o),

      // HWLoop signls
      .pc_id_i(pc_id_i),

      .hwlp_start_addr_i(hwlp_start_o),
      .hwlp_end_addr_i  (hwlp_end_o),
      .hwlp_counter_i   (hwlp_cnt_o),
      .hwlp_dec_cnt_o   (hwlp_dec_cnt),

      .hwlp_jump_o     (hwlp_jump_o),
      .hwlp_targ_addr_o(hwlp_target_o),

      // LSU
      .data_req_ex_i    (data_req_ex_o),
      .data_we_ex_i     (data_we_ex_o),
      .data_misaligned_i(data_misaligned_i),
      .data_load_event_i(data_load_event_id),
      .data_err_i       (data_err_i),
      .data_err_ack_o   (data_err_ack_o),

      // ALU
      .mult_multicycle_i(mult_multicycle_i),

      // APU
      .apu_en_i               (apu_en),
      .apu_read_dep_i         (apu_read_dep_i),
      .apu_read_dep_for_jalr_i(apu_read_dep_for_jalr_i),
      .apu_write_dep_i        (apu_write_dep_i),

      .apu_stall_o(apu_stall),

      // jump/branch control
      .branch_taken_ex_i          (branch_taken_ex),
      .ctrl_transfer_insn_in_id_i (ctrl_transfer_insn_in_id),
      .ctrl_transfer_insn_in_dec_i(ctrl_transfer_insn_in_dec_o),

      // Interrupt signals
      .irq_wu_ctrl_i     (irq_wu_ctrl),
      .irq_req_ctrl_i    (irq_req_ctrl),
      .irq_sec_ctrl_i    (irq_sec_ctrl),
      .irq_id_ctrl_i     (irq_id_ctrl),
      .current_priv_lvl_i(current_priv_lvl_i),
      .irq_ack_o         (irq_ack_o),
      .irq_id_o          (irq_id_o),

      // Debug Signal
      .debug_mode_o          (debug_mode_o),
      .debug_cause_o         (debug_cause_o),
      .debug_csr_save_o      (debug_csr_save_o),
      .debug_req_i           (debug_req_i),
      .debug_single_step_i   (debug_single_step_i),
      .debug_ebreakm_i       (debug_ebreakm_i),
      .debug_ebreaku_i       (debug_ebreaku_i),
      .trigger_match_i       (trigger_match_i),
      .debug_p_elw_no_sleep_o(debug_p_elw_no_sleep_o),
      .debug_wfi_no_sleep_o  (debug_wfi_no_sleep),
      .debug_havereset_o     (debug_havereset_o),
      .debug_running_o       (debug_running_o),
      .debug_halted_o        (debug_halted_o),

      // Wakeup Signal
      .wake_from_sleep_o(wake_from_sleep_o),

      // CSR Controller Signals
      .csr_save_cause_o     (csr_save_cause_o),
      .csr_cause_o          (csr_cause_o),
      .csr_save_if_o        (csr_save_if_o),
      .csr_save_id_o        (csr_save_id_o),
      .csr_save_ex_o        (csr_save_ex_o),
      .csr_restore_mret_id_o(csr_restore_mret_id_o),
      .csr_restore_uret_id_o(csr_restore_uret_id_o),

      .csr_restore_dret_id_o(csr_restore_dret_id_o),

      .csr_irq_sec_o(csr_irq_sec_o),

      // Write targets from ID
      .regfile_we_id_i       (regfile_alu_we_dec_id),
      .regfile_alu_waddr_id_i(regfile_alu_waddr_id),

      // Forwarding signals from regfile
      .regfile_we_ex_i   (regfile_we_ex_o),
      .regfile_waddr_ex_i(regfile_waddr_ex_o),
      .regfile_we_wb_i   (regfile_we_wb_i),

      // regfile port 2
      .regfile_alu_we_fw_i(regfile_alu_we_fw_i),

      // Forwarding detection signals
      .reg_d_ex_is_reg_a_i (reg_d_ex_is_reg_a_id),
      .reg_d_ex_is_reg_b_i (reg_d_ex_is_reg_b_id),
      .reg_d_ex_is_reg_c_i (reg_d_ex_is_reg_c_id),
      .reg_d_wb_is_reg_a_i (reg_d_wb_is_reg_a_id),
      .reg_d_wb_is_reg_b_i (reg_d_wb_is_reg_b_id),
      .reg_d_wb_is_reg_c_i (reg_d_wb_is_reg_c_id),
      .reg_d_alu_is_reg_a_i(reg_d_alu_is_reg_a_id),
      .reg_d_alu_is_reg_b_i(reg_d_alu_is_reg_b_id),
      .reg_d_alu_is_reg_c_i(reg_d_alu_is_reg_c_id),

      // Forwarding signals
      .operand_a_fw_mux_sel_o(operand_a_fw_mux_sel),
      .operand_b_fw_mux_sel_o(operand_b_fw_mux_sel),
      .operand_c_fw_mux_sel_o(operand_c_fw_mux_sel),

      // Stall signals
      .halt_if_o(halt_if),
      .halt_id_o(halt_id),

      .misaligned_stall_o(misaligned_stall),
      .jr_stall_o        (jr_stall),
      .load_stall_o      (load_stall),

      .id_ready_i(id_ready_o),
      .id_valid_i(id_valid_o),

      .ex_valid_i(ex_valid_i),

      .wb_ready_i(wb_ready_i),

      // Performance Counters
      .perf_pipeline_stall_o(perf_pipeline_stall)
  );

  ///////////////////////////////////////////////////////////////////
  //  _____      _       _____             _             _ _
  // |_   _|    | |     /  __ \           | |           | | |
  //   | | _ __ | |_    | /  \/ ___  _ __ | |_ _ __ ___ | | | ___ _ __
  //   | || '_ \| __|   | |    / _ \| '_ \| __| '__/ _ \| | |/ _ \ '__|
  //  _| || | | | |_ _  | \__/\ (_) | | | | |_| | | (_) | | |  __/ |
  //  \___/_| |_|\__(_)  \____/\___/|_| |_|\__|_|  \___/|_|_|\___|_|
  ///////////////////////////////////////////////////////////////////
  // INTERRUPT CONTROLLER INSTANTIATION
  ///////////////////////////////////////////////////////////////////
  // Manages external interrupt requests and priorities
  // - Handles 32 external interrupt lines (irq_i[31:0])
  // - Supports secure interrupts (irq_sec_i) for M-mode only (PULP_SECURE)
  // - Prioritizes interrupts based on ID (lower ID = higher priority)
  // - Interfaces with CSR registers for interrupt enable/pending (MIE/MIP)
  // - Generates wake-up signals for WFI instruction
  // - Respects privilege levels (M-mode vs U-mode interrupt enable)
  
  cv32e40p_int_controller #(
      .PULP_SECURE(PULP_SECURE)
  ) int_controller_i (
      .clk  (clk),
      .rst_n(rst_n),

      // External interrupt lines
      .irq_i    (irq_i),
      .irq_sec_i(irq_sec_i),

      // To cv32e40p_controller
      .irq_req_ctrl_o(irq_req_ctrl),
      .irq_sec_ctrl_o(irq_sec_ctrl),
      .irq_id_ctrl_o (irq_id_ctrl),
      .irq_wu_ctrl_o (irq_wu_ctrl),

      // To/from with cv32e40p_cs_registers
      .mie_bypass_i      (mie_bypass_i),
      .mip_o             (mip_o),
      .m_ie_i            (m_irq_enable_i),
      .u_ie_i            (u_irq_enable_i),
      .current_priv_lvl_i(current_priv_lvl_i)
  );

  generate
    if (COREV_PULP) begin : gen_hwloop_regs

      ///////////////////////////////////////////////////////////////////
      //  _   ___        ___     ___   ___  ____
      // | | | \ \      / / |   / _ \ / _ \|  _ \
      // | |_| |\ \ /\ / /| |  | | | | | | | |_) |
      // |  _  | \ V  V / | |__| |_| | |_| |  __/
      // |_| |_|  \_/\_/  |_____\___/ \___/|_|
      ///////////////////////////////////////////////////////////////////
      // HARDWARE LOOP REGISTERS (PULP Extension)
      ///////////////////////////////////////////////////////////////////
      // Implements zero-overhead hardware loops for efficient loop execution
      // - Supports up to N_HWLP loops (typically 2)
      // - Each loop has: start address, end address, iteration counter
      // - Automatically decrements counter and jumps to start when PC reaches end
      // - No branch penalty - loop back is free (zero overhead)
      // - Loop setup instructions: lp.setup, lp.setupi, lp.start, lp.end, lp.count
      // - Significantly improves performance for tight loops (DSP, signal processing)

      cv32e40p_hwloop_regs #(
          .N_REGS(N_HWLP)
      ) hwloop_regs_i (
          .clk  (clk),
          .rst_n(rst_n),

          // from ID
          .hwlp_start_data_i(hwlp_start),
          .hwlp_end_data_i  (hwlp_end),
          .hwlp_cnt_data_i  (hwlp_cnt),
          .hwlp_we_i        (hwlp_we_masked),
          .hwlp_regid_i     (hwlp_regid),

          // from controller
          .valid_i(hwlp_valid),

          // to hwloop controller
          .hwlp_start_addr_o(hwlp_start_o),
          .hwlp_end_addr_o  (hwlp_end_o),
          .hwlp_counter_o   (hwlp_cnt_o),

          // from hwloop controller
          .hwlp_dec_cnt_i(hwlp_dec_cnt)
      );

      // Hardware loop valid signal
      // Indicates when a valid hardware loop instruction completes ID stage
      assign hwlp_valid = instr_valid_i & clear_instr_valid_o;

      // Hardware loop register ID extraction
      // Bit 7 of destination field (rd[0]) selects which loop register to access
      assign hwlp_regid = instr[7];  // rd contains hwloop register id

      ///////////////////////////////////////////////////////////////////
      // HARDWARE LOOP CONTROL LOGIC
      ///////////////////////////////////////////////////////////////////
      
      // Hardware loop target/end address multiplexer
      // Calculates loop end address from various sources:
      // - 00: PC + zero-extended immediate << 2 (lp.setupi with imm_iz)
      // - 01: PC + zero-extended immediate << 2 (lp.setup with imm_z)
      // - 10: Register value (lp.endi with rs1)
      always_comb begin
        case (hwlp_target_mux_sel)
          2'b00:   hwlp_end = pc_id_i + {imm_iz_type[29:0], 2'b0};  // PC + (imm_iz << 2)
          2'b01:   hwlp_end = pc_id_i + {imm_z_type[29:0], 2'b0};   // PC + (imm_z << 2)
          2'b10:   hwlp_end = operand_a_fw_id;                      // Register-based end
          default: hwlp_end = operand_a_fw_id;
        endcase
      end

      // Hardware loop start address multiplexer
      // Calculates loop start address:
      // - 00: Same as end address (for immediate loop: start at next instruction)
      // - 01: PC + 4 (next instruction after current PC)
      // - 10: Register value (lp.starti with rs1)
      always_comb begin
        case (hwlp_start_mux_sel)
          2'b00:   hwlp_start = hwlp_end;         // Start = end (for setup)
          2'b01:   hwlp_start = pc_id_i + 4;      // Next PC
          2'b10:   hwlp_start = operand_a_fw_id;  // Register-based start
          default: hwlp_start = operand_a_fw_id;
        endcase
      end

      // Hardware loop counter multiplexer
      // Sets initial loop iteration count:
      // - 0: Zero-extended immediate (lp.setupi, lp.counti)
      // - 1: Register value (lp.count with rs1)
      always_comb begin : hwlp_cnt_mux
        case (hwlp_cnt_mux_sel)
          1'b0: hwlp_cnt = imm_iz_type;      // Immediate count
          1'b1: hwlp_cnt = operand_a_fw_id;  // Register-based count
        endcase
        ;
      end

      ///////////////////////////////////////////////////////////////////
      // HARDWARE LOOP WRITE ENABLE MASKING
      ///////////////////////////////////////////////////////////////////
      // Prevent updating hardware loop registers when:
      // - hwlp_mask is asserted (controller about to take interrupt)
      //   - This ensures xEPC points to the hardware loop setup instruction
      //   - Helps verification by making it clear instruction hasn't executed
      // - ID stage is not ready (pipeline stall)
      
      assign hwlp_we_masked = hwlp_we & ~{3{hwlp_mask}} & {3{id_ready_o}};

    end else begin : gen_no_hwloop_regs

      assign hwlp_start_o   = 'b0;
      assign hwlp_end_o     = 'b0;
      assign hwlp_cnt_o     = 'b0;
      assign hwlp_valid     = 'b0;
      assign hwlp_we_masked = 'b0;
      assign hwlp_start     = 'b0;
      assign hwlp_end       = 'b0;
      assign hwlp_cnt       = 'b0;
      assign hwlp_regid     = 'b0;

    end
  endgenerate

  ///////////////////////////////////////////////////////////////////
  //  ___ ____        _______  __  ____ ___ ____  _____ _     ___ _   _ _____
  // |_ _|  _ \      | ____\ \/ / |  _ \_ _|  _ \| ____| |   |_ _| \ | | ____|
  //  | || | | |_____|  _|  \  /  | |_) | || |_) |  _| | |    | ||  \| |  _|
  //  | || |_| |_____| |___ /  \  |  __/| ||  __/| |___| |___ | || |\  | |___
  // |___|____/      |_____/_/\_\ |_|  |___|_|   |_____|_____|___|_| \_|_____|
  ///////////////////////////////////////////////////////////////////
  // ID/EX PIPELINE REGISTER
  ///////////////////////////////////////////////////////////////////
  // Clocked pipeline register between Instruction Decode and Execute stages
  // - Latches all control signals and operands on posedge clk
  // - Handles special cases:
  //   * Reset: Initialize all outputs to safe default values
  //   * Misaligned access: Update address for second part of split access
  //   * Multi-cycle multiply: Update accumulator operand
  //   * Normal operation: Latch new values when id_valid_o asserted
  // - Registers ~50+ signals including:
  //   * ALU control and operands
  //   * Multiplier control and operands
  //   * APU/FPU control and operands
  //   * Register write addresses and enables
  //   * CSR access control
  //   * Load/store control
  //   * PC value
  //   * Branch indication

  always_ff @(posedge clk, negedge rst_n) begin : ID_EX_PIPE_REGISTERS
    if (rst_n == 1'b0) begin
      // RESET: Initialize all pipeline registers to safe defaults
      
      // ALU control signals
      alu_en_ex_o            <= '0;
      alu_operator_ex_o      <= ALU_SLTU;       // Default ALU operation
      alu_operand_a_ex_o     <= '0;
      alu_operand_b_ex_o     <= '0;
      alu_operand_c_ex_o     <= '0;
      bmask_a_ex_o           <= '0;
      bmask_b_ex_o           <= '0;
      imm_vec_ext_ex_o       <= '0;
      alu_vec_mode_ex_o      <= '0;
      alu_clpx_shift_ex_o    <= 2'b0;          // Complex number shift
      alu_is_clpx_ex_o       <= 1'b0;          // Complex operation flag
      alu_is_subrot_ex_o     <= 1'b0;          // Sub-rotation flag

      // Multiplier control signals
      mult_operator_ex_o     <= MUL_MAC32;      // Default multiply operation
      mult_operand_a_ex_o    <= '0;
      mult_operand_b_ex_o    <= '0;
      mult_operand_c_ex_o    <= '0;
      mult_en_ex_o           <= 1'b0;
      mult_sel_subword_ex_o  <= 1'b0;
      mult_signed_mode_ex_o  <= 2'b00;         // Unsigned x Unsigned
      mult_imm_ex_o          <= '0;

      // Dot product and complex multiply signals (PULP)
      mult_dot_op_a_ex_o     <= '0;
      mult_dot_op_b_ex_o     <= '0;
      mult_dot_op_c_ex_o     <= '0;
      mult_dot_signed_ex_o   <= '0;
      mult_is_clpx_ex_o      <= 1'b0;
      mult_clpx_shift_ex_o   <= 2'b0;
      mult_clpx_img_ex_o     <= 1'b0;          // Complex imaginary part

      // APU/FPU control signals
      apu_en_ex_o            <= '0;
      apu_op_ex_o            <= '0;
      apu_lat_ex_o           <= '0;
      apu_operands_ex_o[0]   <= '0;
      apu_operands_ex_o[1]   <= '0;
      apu_operands_ex_o[2]   <= '0;
      apu_flags_ex_o         <= '0;
      apu_waddr_ex_o         <= '0;

      // Register file write control
      regfile_waddr_ex_o     <= 6'b0;
      regfile_we_ex_o        <= 1'b0;
      regfile_alu_waddr_ex_o <= 6'b0;
      regfile_alu_we_ex_o    <= 1'b0;
      prepost_useincr_ex_o   <= 1'b0;          // Post-increment flag

      // CSR control
      csr_access_ex_o        <= 1'b0;
      csr_op_ex_o            <= CSR_OP_READ;

      // Load/store control
      data_we_ex_o           <= 1'b0;          // Write enable (0=load, 1=store)
      data_type_ex_o         <= 2'b0;          // Data type (byte/half/word)
      data_sign_ext_ex_o     <= 2'b0;          // Sign extension control
      data_reg_offset_ex_o   <= 2'b0;          // Register offset
      data_req_ex_o          <= 1'b0;          // Data request
      data_load_event_ex_o   <= 1'b0;          // Load event (cv.elw)
      atop_ex_o              <= 5'b0;           // Atomic operation type

      data_misaligned_ex_o   <= 1'b0;          // Misaligned access flag

      // PC and branch control
      pc_ex_o                <= '0;
      branch_in_ex_o         <= 1'b0;

    end else if (data_misaligned_i) begin
      ///////////////////////////////////////////////////////////////////
      // MISALIGNED DATA ACCESS CASE
      ///////////////////////////////////////////////////////////////////
      // When a misaligned access occurs, handle the second part of split access
      // Only update necessary signals for address calculation
      
      if (ex_ready_i) begin  // EX stage ready to accept second part

        // Update operand A for post-increment addressing
        // For post-increment, preserve original register value for second access
        if (prepost_useincr_ex_o == 1'b1) begin
          alu_operand_a_ex_o <= operand_a_fw_id;  // Keep original base address
        end

        // Update operand B to add 4 for second word access
        alu_operand_b_ex_o   <= 32'h4;
        
        // Disable register write for second part (only first part writes back)
        regfile_alu_we_ex_o  <= 1'b0;
        
        // Maintain post-increment flag
        prepost_useincr_ex_o <= 1'b1;

        // Set misaligned flag to indicate split access in progress
        data_misaligned_ex_o <= 1'b1;
      end
      
    end else if (mult_multicycle_i) begin
      ///////////////////////////////////////////////////////////////////
      // MULTI-CYCLE MULTIPLIER CASE
      ///////////////////////////////////////////////////////////////////
      // Update accumulator operand C during multi-cycle multiply operations
      // (e.g., MAC instructions that take multiple cycles)
      mult_operand_c_ex_o <= operand_c_fw_id;
      
    end else begin
      ///////////////////////////////////////////////////////////////////
      // NORMAL PIPELINE OPERATION
      ///////////////////////////////////////////////////////////////////
      // Latch all new values from ID stage when pipeline advances

      if (id_valid_o) begin  // ID stage has valid instruction to pass to EX
        
        // ALU control and operands
        alu_en_ex_o <= alu_en;
        if (alu_en) begin
          alu_operator_ex_o  <= alu_operator;
          alu_operand_a_ex_o <= alu_operand_a;
          
          // Special handling for CLIP/CLIPU: mask upper bit of operand B
          if (alu_op_b_mux_sel == OP_B_REGB_OR_FWD && (alu_operator == ALU_CLIP || alu_operator == ALU_CLIPU)) begin
            alu_operand_b_ex_o <= {1'b0, alu_operand_b[30:0]};  // Clear bit 31
          end else begin
            alu_operand_b_ex_o <= alu_operand_b;
          end
          
          alu_operand_c_ex_o  <= alu_operand_c;
          bmask_a_ex_o        <= bmask_a_id;
          bmask_b_ex_o        <= bmask_b_id;
          imm_vec_ext_ex_o    <= imm_vec_ext_id;
          alu_vec_mode_ex_o   <= alu_vec_mode;
          alu_is_clpx_ex_o    <= is_clpx;
          alu_clpx_shift_ex_o <= instr[14:13];  // Extract shift amount from instruction
          alu_is_subrot_ex_o  <= is_subrot;
        end

        // Multiplier control and operands
        mult_en_ex_o <= mult_en;
        if (mult_int_en) begin
          // Integer multiplication (MUL, MULH, MULHSU, MULHU)
          mult_operator_ex_o    <= mult_operator;
          mult_sel_subword_ex_o <= mult_sel_subword;  // 16-bit or 8-bit subword multiply
          mult_signed_mode_ex_o <= mult_signed_mode;  // Sign mode (UxU, SxU, UxS, SxS)
          mult_operand_a_ex_o   <= alu_operand_a;
          mult_operand_b_ex_o   <= alu_operand_b;
          mult_operand_c_ex_o   <= alu_operand_c;     // For MAC (multiply-accumulate)
          mult_imm_ex_o         <= mult_imm_id;
        end
        if (mult_dot_en) begin
          // Dot product operations (PULP extension)
          mult_operator_ex_o   <= mult_operator;
          mult_dot_signed_ex_o <= mult_dot_signed;    // Mixed signed/unsigned dot products
          mult_dot_op_a_ex_o   <= alu_operand_a;
          mult_dot_op_b_ex_o   <= alu_operand_b;
          mult_dot_op_c_ex_o   <= alu_operand_c;
          mult_is_clpx_ex_o    <= is_clpx;            // Complex number operation
          mult_clpx_shift_ex_o <= instr[14:13];       // Complex shift amount
          mult_clpx_img_ex_o   <= instr[25];          // Imaginary part flag
        end

        // APU/FPU pipeline signals
        apu_en_ex_o <= apu_en;
        if (apu_en) begin
          apu_op_ex_o       <= apu_op;          // APU operation code
          apu_lat_ex_o      <= apu_lat;         // Operation latency
          apu_operands_ex_o <= apu_operands;    // Up to 3 operands
          apu_flags_ex_o    <= apu_flags;       // FP rounding mode, formats, etc.
          apu_waddr_ex_o    <= apu_waddr;       // Write-back register address
        end

        // Register file write control (WB stage)
        regfile_we_ex_o <= regfile_we_id;
        if (regfile_we_id) begin
          regfile_waddr_ex_o <= regfile_waddr_id;  // Destination register
        end

        // Register file write control (ALU fast path)
        regfile_alu_we_ex_o <= regfile_alu_we_id;
        if (regfile_alu_we_id) begin
          regfile_alu_waddr_ex_o <= regfile_alu_waddr_id;  // ALU destination register
        end

        // Post-increment addressing flag (PULP)
        prepost_useincr_ex_o <= prepost_useincr;

        // CSR access control
        csr_access_ex_o      <= csr_access;
        csr_op_ex_o          <= csr_op;        // CSR operation (RW, RS, RC)

        // Load/store unit control
        data_req_ex_o        <= data_req_id;
        if (data_req_id) begin  // Only update LSU signals when there's an active request
          data_we_ex_o         <= data_we_id;           // Write enable (0=load, 1=store)
          data_type_ex_o       <= data_type_id;         // Data size (byte/half/word)
          data_sign_ext_ex_o   <= data_sign_ext_id;     // Sign extension for loads
          data_reg_offset_ex_o <= data_reg_offset_id;   // Register-indexed offset
          data_load_event_ex_o <= data_load_event_id;   // Event load (cv.elw)
          atop_ex_o            <= atop_id;              // Atomic operation type
        end else begin
          data_load_event_ex_o <= 1'b0;
        end

        // Clear misaligned flag for new instruction
        data_misaligned_ex_o <= 1'b0;

        // Program counter (for branches and memory exceptions)
        if ((ctrl_transfer_insn_in_id == BRANCH_COND) || data_req_id) begin
          pc_ex_o <= pc_id_i;  // Save PC for branch resolution or memory exception
        end

        // Branch flag (for branch prediction and PC control)
        branch_in_ex_o <= ctrl_transfer_insn_in_id == BRANCH_COND;
        
      end else if (ex_ready_i) begin
        ///////////////////////////////////////////////////////////////////
        // PIPELINE BUBBLE INSERTION
        ///////////////////////////////////////////////////////////////////
        // EX stage is ready but ID doesn't have a valid instruction
        // Insert a bubble (NOP) by disabling all write enables
        
        regfile_we_ex_o      <= 1'b0;     // Disable register write
        regfile_alu_we_ex_o  <= 1'b0;     // Disable ALU write
        csr_op_ex_o          <= CSR_OP_READ;  // No CSR write
        data_req_ex_o        <= 1'b0;     // No memory request
        data_load_event_ex_o <= 1'b0;     // No load event
        data_misaligned_ex_o <= 1'b0;     // No misaligned access
        branch_in_ex_o       <= 1'b0;     // No branch
        apu_en_ex_o          <= 1'b0;     // No APU operation
        alu_operator_ex_o    <= ALU_SLTU; // Default ALU op (harmless)
        mult_en_ex_o         <= 1'b0;     // No multiplication
        alu_en_ex_o          <= 1'b1;     // Keep ALU enabled (for forwarding path)

      end else if (csr_access_ex_o) begin
        ///////////////////////////////////////////////////////////////////
        // CSR ACCESS STALL HANDLING
        ///////////////////////////////////////////////////////////////////
        // In the EX stage there was a CSR access
        // Disable regfile_alu_we_ex_o to avoid multiple writes to RF
        // This prevents overwriting RF with current CSR value instead of old one
        regfile_alu_we_ex_o <= 1'b0;
      end
    end
  end

  ///////////////////////////////////////////////////////////////////
  // PERFORMANCE COUNTER EVENTS
  ///////////////////////////////////////////////////////////////////
  // Track various pipeline events for performance monitoring
  // These feed into the mhpmcounter CSRs for profiling

  // Instruction retirement counter
  // Count valid instructions that complete ID stage (excluding illegal/ebreak/ecall)
  // Note: Counts issued instructions, not necessarily completed ones
  //       CSR instruction handling ensures this matches retired instruction count
  assign minstret = id_valid_o && is_decoding_o && !(illegal_insn_dec || ebrk_insn_dec || ecall_insn_dec);

  ///////////////////////////////////////////////////////////////////
  // PERFORMANCE COUNTER REGISTER OUTPUTS
  ///////////////////////////////////////////////////////////////////
  // Register all performance counter events for timing closure
  // These outputs connect to the CSR module's mhpmevent inputs
  
  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      // Reset: Initialize all performance counters
      id_valid_q               <= 1'b0;
      mhpmevent_minstret_o     <= 1'b0;  // Instructions retired
      mhpmevent_load_o         <= 1'b0;  // Load instructions
      mhpmevent_store_o        <= 1'b0;  // Store instructions
      mhpmevent_jump_o         <= 1'b0;  // Jump instructions (JAL/JALR)
      mhpmevent_branch_o       <= 1'b0;  // Branch instructions
      mhpmevent_compressed_o   <= 1'b0;  // Compressed (16-bit) instructions
      mhpmevent_branch_taken_o <= 1'b0;  // Taken branches
      mhpmevent_jr_stall_o     <= 1'b0;  // Jump-register stalls
      mhpmevent_imiss_o        <= 1'b0;  // Instruction cache misses
      mhpmevent_ld_stall_o     <= 1'b0;  // Load-use stalls
      mhpmevent_pipe_stall_o   <= 1'b0;  // Pipeline stalls
    end else begin
      // Helper signal for edge detection (detect first cycle of stall)
      id_valid_q <= id_valid_o;
      
      // ID stage event counters (count when instruction is valid and retiring)
      mhpmevent_minstret_o <= minstret;  // Retired instructions
      
      // Load instructions: retired instruction + data request + not a write
      mhpmevent_load_o <= minstret && data_req_id && !data_we_id;
      
      // Store instructions: retired instruction + data request + write enable
      mhpmevent_store_o <= minstret && data_req_id && data_we_id;
      
      // Jump instructions: JAL (unconditional) or JALR (register-based)
      mhpmevent_jump_o <= minstret && ((ctrl_transfer_insn_in_id == BRANCH_JAL) || 
                                       (ctrl_transfer_insn_in_id == BRANCH_JALR));
      
      // Conditional branch instructions (BEQ, BNE, BLT, BGE, BLTU, BGEU)
      mhpmevent_branch_o <= minstret && (ctrl_transfer_insn_in_id == BRANCH_COND);
      
      // Compressed (RVC) instructions (16-bit encoding)
      mhpmevent_compressed_o <= minstret && is_compressed_i;
      
      // EX stage event counter
      // Taken branches: branch instruction AND branch condition evaluated true
      mhpmevent_branch_taken_o <= mhpmevent_branch_o && branch_decision_i;
      
      // IF stage event counter
      // Instruction cache misses (from prefetch buffer)
      mhpmevent_imiss_o <= perf_imiss_i;
      
      // Jump-register hazard stalls
      // Count stalls due to JALR reading a register that's being written
      // Use id_valid_q to only count the first cycle of each stall
      // Don't count stalls on flushed instructions (halt_id check)
      mhpmevent_jr_stall_o <= jr_stall && !halt_id && id_valid_q;
      
      // Load-use hazard stalls
      // Count stalls due to instruction reading a register being loaded
      // Use id_valid_q to only count the first cycle of each stall
      // Don't count stalls on flushed instructions (halt_id check)
      mhpmevent_ld_stall_o <= load_stall && !halt_id && id_valid_q;
      
      // Pipeline stalls (includes ELW event loads, APU multi-cycle, etc.)
      mhpmevent_pipe_stall_o <= perf_pipeline_stall;
    end
  end

  ///////////////////////////////////////////////////////////////////
  // PIPELINE CONTROL OUTPUTS
  ///////////////////////////////////////////////////////////////////
  // ID stage ready when not stalled by any hazard and EX stage is ready
  // Stall sources:
  // - misaligned_stall: Misaligned memory access (split into 2 accesses)
  // - jr_stall: Jump-register reads register being written (RAW hazard)
  // - load_stall: Instruction reads register being loaded (load-use hazard)
  // - apu_stall: APU dependency or busy
  // - csr_apu_stall: CSR access while APU is busy
  assign id_ready_o = ((~misaligned_stall) & (~jr_stall) & (~load_stall) & (~apu_stall) & (~csr_apu_stall) & ex_ready_i);
  
  // ID stage valid when not halted and ready to advance
  assign id_valid_o = (~halt_id) & id_ready_o;
  
  // Halt IF stage when ID stage is halted (exception/interrupt/debug)
  assign halt_if_o = halt_if;

  ///////////////////////////////////////////////////////////////////
  // ASSERTIONS
  ///////////////////////////////////////////////////////////////////
  // Formal verification assertions to check design invariants
  // Only included when CV32E40P_ASSERT_ON is defined
  
`ifdef CV32E40P_ASSERT_ON

  always_comb begin
    if (FPU == 1) begin
      assert (APU_NDSFLAGS_CPU >= C_RM+2*cv32e40p_fpu_pkg::FP_FORMAT_BITS+cv32e40p_fpu_pkg::INT_FORMAT_BITS)
      else
        $error("[apu] APU_NDSFLAGS_CPU APU flagbits is smaller than %0d",
               C_RM + 2 * cv32e40p_fpu_pkg::FP_FORMAT_BITS + cv32e40p_fpu_pkg::INT_FORMAT_BITS);
    end
  end

  // make sure that branch decision is valid when jumping
  a_br_decision :
  assert property (@(posedge clk) (branch_in_ex_o) |-> (branch_decision_i !== 1'bx))
  else begin
    $warning("%t, Branch decision is X in module %m", $time);
    $stop;
  end

  // the instruction delivered to the ID stage should always be valid
  a_valid_instr :
  assert property (@(posedge clk) (instr_valid_i & (~illegal_c_insn_i)) |-> (!$isunknown(instr)))
  else $warning("%t, Instruction is valid, but has at least one X", $time);

  // Check that instruction after taken branch is flushed (more should actually be flushed, but that is not checked here)
  // and that EX stage is ready to receive flushed instruction immediately
  property p_branch_taken_ex;
    @(posedge clk) disable iff (!rst_n) (branch_taken_ex == 1'b1) |-> ((ex_ready_i == 1'b1) &&
                                                                          (alu_en == 1'b0) && (apu_en == 1'b0) &&
                                                                          (mult_en == 1'b0) && (mult_int_en == 1'b0) &&
                                                                          (mult_dot_en == 1'b0) && (regfile_we_id == 1'b0) &&
                                                                          (regfile_alu_we_id == 1'b0) && (data_req_id == 1'b0));
  endproperty

  a_branch_taken_ex :
  assert property (p_branch_taken_ex);

  // Check that if IRQ PC update does not coincide with IRQ related CSR write
  // MIE is excluded from the check because it has a bypass.
  property p_irq_csr;
    @(posedge clk) disable iff (!rst_n) (pc_set_o && (pc_mux_o == PC_EXCEPTION) && ((exc_pc_mux_o == EXC_PC_EXCEPTION) || (exc_pc_mux_o == EXC_PC_IRQ)) &&
                                            csr_access_ex_o && (csr_op_ex_o != CSR_OP_READ)) |->
                                           ((alu_operand_b_ex_o[11:0] != CSR_MSTATUS) && (alu_operand_b_ex_o[11:0] != CSR_USTATUS) &&
                                            (alu_operand_b_ex_o[11:0] != CSR_MEPC) && (alu_operand_b_ex_o[11:0] != CSR_UEPC) &&
                                            (alu_operand_b_ex_o[11:0] != CSR_MCAUSE) && (alu_operand_b_ex_o[11:0] != CSR_UCAUSE) &&
                                            (alu_operand_b_ex_o[11:0] != CSR_MTVEC) && (alu_operand_b_ex_o[11:0] != CSR_UTVEC));
  endproperty

  a_irq_csr :
  assert property (p_irq_csr);

  // Check that xret does not coincide with CSR write (to avoid using wrong return address)
  // This check is more strict than really needed; a CSR instruction would be allowed in EX as long
  // as its write action happens before the xret CSR usage
  property p_xret_csr;
    @(posedge clk) disable iff (!rst_n) (pc_set_o && ((pc_mux_o == PC_MRET) || (pc_mux_o == PC_URET) || (pc_mux_o == PC_DRET))) |->
                                           (!(csr_access_ex_o && (csr_op_ex_o != CSR_OP_READ)));
  endproperty

  a_xret_csr :
  assert property (p_xret_csr);

  generate
    if (!A_EXTENSION) begin : gen_no_a_extension_assertions

      // Check that A extension opcodes are decoded as illegal when A extension not enabled
      property p_illegal_0;
        @(posedge clk) disable iff (!rst_n) (instr[6:0] == OPCODE_AMO) |-> (illegal_insn_dec == 'b1);
      endproperty

      a_illegal_0 :
      assert property (p_illegal_0);

    end
  endgenerate

  generate
    if (!COREV_PULP) begin : gen_no_pulp_xpulp_assertions

      // Check that PULP extension opcodes are decoded as illegal when PULP extension is not enabled
      property p_illegal_1;
        @(posedge clk) disable iff (!rst_n) ((instr[6:0] == OPCODE_CUSTOM_0) || (instr[6:0] == OPCODE_CUSTOM_1) ||
                                             (instr[6:0] == OPCODE_CUSTOM_2) || (instr[6:0] == OPCODE_CUSTOM_3))
                                            |-> (illegal_insn_dec == 'b1);
      endproperty

      a_illegal_1 :
      assert property (p_illegal_1);

      // Check that certain ALU operations are not used when PULP extension is not enabled
      property p_alu_op;
        @(posedge clk) disable iff (!rst_n) (1'b1) |-> ( (alu_operator != ALU_ADDU ) && (alu_operator != ALU_SUBU ) &&
                                                           (alu_operator != ALU_ADDR ) && (alu_operator != ALU_SUBR ) &&
                                                           (alu_operator != ALU_ADDUR) && (alu_operator != ALU_SUBUR) &&
                                                           (alu_operator != ALU_ROR) && (alu_operator != ALU_BEXT) &&
                                                           (alu_operator != ALU_BEXTU) && (alu_operator != ALU_BINS) &&
                                                           (alu_operator != ALU_BCLR) && (alu_operator != ALU_BSET) &&
                                                           (alu_operator != ALU_BREV) && (alu_operator != ALU_FF1) &&
                                                           (alu_operator != ALU_FL1) && (alu_operator != ALU_CNT) &&
                                                           (alu_operator != ALU_CLB) && (alu_operator != ALU_EXTS) &&
                                                           (alu_operator != ALU_EXT) && (alu_operator != ALU_LES) &&
                                                           (alu_operator != ALU_LEU) && (alu_operator != ALU_GTS) &&
                                                           (alu_operator != ALU_GTU) && (alu_operator != ALU_SLETS) &&
                                                           (alu_operator != ALU_SLETU) && (alu_operator != ALU_ABS) &&
                                                           (alu_operator != ALU_CLIP) && (alu_operator != ALU_CLIPU) &&
                                                           (alu_operator != ALU_INS) && (alu_operator != ALU_MIN) &&
                                                           (alu_operator != ALU_MINU) && (alu_operator != ALU_MAX) &&
                                                           (alu_operator != ALU_MAXU) && (alu_operator != ALU_SHUF) &&
                                                           (alu_operator != ALU_SHUF2) && (alu_operator != ALU_PCKLO) &&
                                                           (alu_operator != ALU_PCKHI) );
      endproperty

      a_alu_op :
      assert property (p_alu_op);

      // Check that certain vector modes are not used when PULP extension is not enabled
      property p_vector_mode;
        @(posedge clk) disable iff (!rst_n) (1'b1) |-> ( (alu_vec_mode != VEC_MODE8 ) && (alu_vec_mode != VEC_MODE16 ) );
      endproperty

      a_vector_mode :
      assert property (p_vector_mode);

      // Check that certain multiplier operations are not used when PULP extension is not enabled
      property p_mul_op;
        @(posedge clk) disable iff (!rst_n) (mult_int_en == 1'b1) |-> ( (mult_operator != MUL_MSU32) && (mult_operator != MUL_I) &&
                                                                         (mult_operator != MUL_IR) && (mult_operator != MUL_DOT8) &&
                                                                         (mult_operator != MUL_DOT16) );
      endproperty

      a_mul_op :
      assert property (p_mul_op);

    end
  endgenerate

  // Check that illegal instruction has no other side effects
  property p_illegal_2;
    @(posedge clk) disable iff (!rst_n) (illegal_insn_dec == 1'b1) |-> !(ebrk_insn_dec || mret_insn_dec || uret_insn_dec || dret_insn_dec ||
                                                                            ecall_insn_dec || wfi_insn_dec || fencei_insn_dec ||
                                                                            alu_en || mult_int_en || mult_dot_en || apu_en ||
                                                                            regfile_we_id || regfile_alu_we_id ||
                                                                            csr_op != CSR_OP_READ || data_req_id);
  endproperty

  a_illegal_2 :
  assert property (p_illegal_2);

`endif

endmodule  // cv32e40p_id_stage
