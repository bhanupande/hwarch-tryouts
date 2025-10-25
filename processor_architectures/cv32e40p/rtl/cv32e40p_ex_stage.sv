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
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Execute stage                                              //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Execution stage: Hosts ALU and MAC unit                    //
//                 ALU: computes additions/subtractions/comparisons           //
//                 MULT: computes normal multiplications                      //
//                 APU_DISP: offloads instructions to the shared unit.        //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Module: cv32e40p_ex_stage
///////////////////////////////////////////////////////////////////////////////
//
// FUNCTION:
//   Execute (EX) stage - third stage of the 4-stage pipeline.
//   Performs arithmetic, logic, multiplication, and offloads to APU/FPU.
//
// PIPELINE POSITION:
//   IF → ID → EX → WB
//          ^
//          This module
//
// RESPONSIBILITIES:
//   1. Arithmetic & Logic:
//      - Integer ALU operations (add, sub, shift, logic, compare)
//      - PULP vector operations (SIMD)
//      - Complex number operations (COREV_PULP)
//
//   2. Multiplication:
//      - Single-cycle multiply (MUL)
//      - Multi-cycle multiply high (MULH)
//      - Dot product operations (PULP)
//
//   3. APU/FPU Offload (FPU=1):
//      - Dispatch floating-point operations to APU
//      - Manage multi-cycle FP operations
//      - Handle result writeback conflicts
//
//   4. Branch Resolution:
//      - Calculate branch target (jump_target_o)
//      - Evaluate branch condition (branch_decision_o)
//
//   5. Result Writeback:
//      - Forward results to ID stage (bypassing)
//      - Write results to register file via WB stage
//      - Manage two writeback ports (ALU port, LSU port)
//
// DUAL WRITEBACK PORTS:
//   Why two ports?
//     - ALU Port: ALU, MULT, CSR, single-cycle APU, multi-cycle APU (>2 cycles)
//     - LSU Port: Load results, two-cycle APU operations
//   
//   Prevents writeback conflicts between:
//     - Load and ALU/MULT
//     - APU and ALU/MULT
//
// APU OPERATION TYPES (FPU=1):
//   1. Single-cycle: Complete in 1 cycle (rare, e.g., FP move)
//   2. Two-cycle: Complete in 2 cycles (uses LSU writeback port)
//   3. Multi-cycle: >2 cycles (uses ALU writeback port)
//
//   Memorization register:
//     - Saves multi-cycle APU result if writeback stalled
//     - Prevents result loss during conflicts
//
// PIPELINE CONTROL:
//   ex_ready_o: EX ready to accept new instruction
//     - All units ready (ALU, MULT, LSU)
//     - WB stage ready
//     - No writeback contention
//     - Special case: branches bypass WB (immediate ready)
//
//   ex_valid_o: EX producing valid result
//     - At least one unit active
//     - All units ready for completion
//     - WB stage ready
//
// FORWARDING:
//   Results forwarded to ID stage for data hazard resolution:
//     - ALU/MULT results available same cycle
//     - CSR read results
//     - APU results (when complete)
//
// TIMING:
//   - ALU: Single cycle (combinational)
//   - MULT: 1-4 cycles (MUL=1, MULH=2-4)
//   - APU: 1-many cycles (latency specified by apu_lat_i)
//   - Branch: Resolved in EX, no WB needed
//
///////////////////////////////////////////////////////////////////////////////

module cv32e40p_ex_stage
  import cv32e40p_pkg::*;
  import cv32e40p_apu_core_pkg::*;
#(
    // PULP ISA Extension (vector ops, dot products)
    parameter COREV_PULP       = 0,
    
    // Floating-point unit enable (APU offload)
    parameter FPU              = 0,
    
    // APU configuration parameters
    // Number of operands per APU instruction
    parameter APU_NARGS_CPU    = 3,
    
    // APU operation code width
    parameter APU_WOP_CPU      = 6,
    
    // APU downstream flags (APU → CPU)
    parameter APU_NDSFLAGS_CPU = 15,
    
    // APU upstream flags (CPU → APU, e.g., FP rounding mode)
    parameter APU_NUSFLAGS_CPU = 5
) (
    // ===== Clock and Reset =====
    input logic clk,
    input logic rst_n,

    // ===== ALU Control Signals from ID Stage =====
    // alu_operator_i: ALU operation to perform
    //   - ADD, SUB, SLT, AND, OR, XOR, shifts, etc.
    input alu_opcode_e        alu_operator_i,
    
    // alu_operand_a_i: First ALU operand
    //   - Typically rs1 or PC
    input logic        [31:0] alu_operand_a_i,
    
    // alu_operand_b_i: Second ALU operand
    //   - Typically rs2 or immediate
    input logic        [31:0] alu_operand_b_i,
    
    // alu_operand_c_i: Third ALU operand
    //   - Used for branch target calculation
    input logic        [31:0] alu_operand_c_i,
    
    // alu_en_i: ALU operation enable
    input logic               alu_en_i,
    
    // bmask_a_i, bmask_b_i: Bit manipulation masks (PULP)
    input logic        [ 4:0] bmask_a_i,
    input logic        [ 4:0] bmask_b_i,
    
    // imm_vec_ext_i: Vector immediate extension mode (PULP)
    input logic        [ 1:0] imm_vec_ext_i,
    
    // alu_vec_mode_i: Vector operation mode (PULP SIMD)
    //   - 8-bit, 16-bit SIMD modes
    input logic        [ 1:0] alu_vec_mode_i,
    
    // alu_is_clpx_i: Complex number operation (PULP)
    input logic               alu_is_clpx_i,
    
    // alu_is_subrot_i: Sub-rotation operation (PULP)
    input logic               alu_is_subrot_i,
    
    // alu_clpx_shift_i: Complex number shift amount (PULP)
    input logic        [ 1:0] alu_clpx_shift_i,

    // ===== Multiplier Control Signals =====
    // mult_operator_i: Multiplier operation
    //   - MUL, MULH, MULHSU, MULHU
    input mul_opcode_e        mult_operator_i,
    
    // mult_operand_a/b/c_i: Multiplier operands
    input logic        [31:0] mult_operand_a_i,
    input logic        [31:0] mult_operand_b_i,
    input logic        [31:0] mult_operand_c_i,
    
    // mult_en_i: Multiplier enable
    input logic               mult_en_i,
    
    // mult_sel_subword_i: Subword multiplication (16x16)
    input logic               mult_sel_subword_i,
    
    // mult_signed_mode_i: Sign mode (signed/unsigned)
    input logic        [ 1:0] mult_signed_mode_i,
    
    // mult_imm_i: Immediate for multiply-accumulate
    input logic        [ 4:0] mult_imm_i,

    // ===== Dot Product Signals (PULP) =====
    // Dot product: sum of element-wise products
    input logic [31:0] mult_dot_op_a_i,
    input logic [31:0] mult_dot_op_b_i,
    input logic [31:0] mult_dot_op_c_i,
    input logic [ 1:0] mult_dot_signed_i,
    input logic        mult_is_clpx_i,
    input logic [ 1:0] mult_clpx_shift_i,
    input logic        mult_clpx_img_i,

    // mult_multicycle_o: Multiplier needs multiple cycles
    //   - High for MULH operations
    output logic mult_multicycle_o,

    // ===== LSU Status Signals =====
    // data_req_i: Data memory request active
    input logic data_req_i,
    
    // data_rvalid_i: Data memory response valid
    input logic data_rvalid_i,
    
    // data_misaligned_ex_i: Misaligned access in EX
    input logic data_misaligned_ex_i,
    
    // data_misaligned_i: Misaligned access detected
    input logic data_misaligned_i,

    // ctrl_transfer_insn_in_dec_i: Control transfer in decode
    //   - Used for APU dependency checking
    input logic [1:0] ctrl_transfer_insn_in_dec_i,

    // ===== FPU Flags Output =====
    // fpu_fflags_we_o: FP flags write enable
    //   - Update fflags CSR
    output logic fpu_fflags_we_o,
    
    // fpu_fflags_o: FP exception flags
    //   - NV, DZ, OF, UF, NX (invalid, divide-by-zero, overflow, underflow, inexact)
    output logic [APU_NUSFLAGS_CPU-1:0] fpu_fflags_o,

    // ===== APU Control Signals =====
    // apu_en_i: APU operation enable
    input logic                              apu_en_i,
    
    // apu_op_i: APU operation code
    input logic [     APU_WOP_CPU-1:0]       apu_op_i,
    
    // apu_lat_i: APU operation latency
    //   - 0: single-cycle, 1: two-cycle, 2+: multi-cycle
    input logic [                 1:0]       apu_lat_i,
    
    // apu_operands_i: APU operands (up to 3)
    input logic [   APU_NARGS_CPU-1:0][31:0] apu_operands_i,
    
    // apu_waddr_i: APU result destination register
    input logic [                 5:0]       apu_waddr_i,
    
    // apu_flags_i: APU control flags (rounding mode, etc.)
    input logic [APU_NUSFLAGS_CPU-1:0]       apu_flags_i,

    // ===== APU Dependency Tracking =====
    // apu_read_regs_i: Source register addresses
    input  logic [2:0][5:0] apu_read_regs_i,
    
    // apu_read_regs_valid_i: Which sources are valid
    input  logic [2:0]      apu_read_regs_valid_i,
    
    // apu_read_dep_o: Read-after-write dependency
    output logic            apu_read_dep_o,
    
    // apu_read_dep_for_jalr_o: Dependency for JALR
    output logic            apu_read_dep_for_jalr_o,
    
    // apu_write_regs_i: Destination register addresses
    input  logic [1:0][5:0] apu_write_regs_i,
    
    // apu_write_regs_valid_i: Which destinations valid
    input  logic [1:0]      apu_write_regs_valid_i,
    
    // apu_write_dep_o: Write-after-write dependency
    output logic            apu_write_dep_o,

    // ===== APU Performance Counters =====
    // apu_perf_type_o: APU operation type
    output logic apu_perf_type_o,
    
    // apu_perf_cont_o: APU contention
    output logic apu_perf_cont_o,
    
    // apu_perf_wb_o: APU writeback conflict
    output logic apu_perf_wb_o,

    // ===== APU Status =====
    // apu_busy_o: APU operation in progress
    output logic apu_busy_o,
    
    // apu_ready_wb_o: APU ready for writeback
    output logic apu_ready_wb_o,

    // ===== APU Interconnect (to external FPU) =====
    // Handshake signals
    // apu_req_o: APU request
    output logic                           apu_req_o,
    
    // apu_gnt_i: APU grant
    input  logic                           apu_gnt_i,
    
    // Request channel
    // apu_operands_o: Operands to APU
    output logic [APU_NARGS_CPU-1:0][31:0] apu_operands_o,
    
    // apu_op_o: Operation code to APU
    output logic [  APU_WOP_CPU-1:0]       apu_op_o,
    
    // Response channel
    // apu_rvalid_i: APU result valid
    input  logic                           apu_rvalid_i,
    
    // apu_result_i: APU result data
    input  logic [             31:0]       apu_result_i,

    // ===== LSU Interface =====
    // lsu_en_i: Load/store operation enable
    input logic        lsu_en_i,
    
    // lsu_rdata_i: Load data from memory
    input logic [31:0] lsu_rdata_i,

    // ===== Register File Writeback Info from ID =====
    // branch_in_ex_i: Branch instruction in EX
    //   - Branches don't need WB stage
    input logic       branch_in_ex_i,
    
    // regfile_alu_waddr_i: ALU result destination register
    input logic [5:0] regfile_alu_waddr_i,
    
    // regfile_alu_we_i: ALU result write enable
    input logic       regfile_alu_we_i,

    // ===== Pass-through to WB (for LSU) =====
    // regfile_we_i: Register write enable (LSU port)
    input logic       regfile_we_i,
    
    // regfile_waddr_i: Destination register (LSU port)
    input logic [5:0] regfile_waddr_i,

    // ===== CSR Access =====
    // csr_access_i: CSR read/write operation
    input logic        csr_access_i,
    
    // csr_rdata_i: CSR read data
    input logic [31:0] csr_rdata_i,

    // ===== WB Stage Output (LSU Port) =====
    // regfile_waddr_wb_o: Destination register
    output logic [ 5:0] regfile_waddr_wb_o,
    
    // regfile_we_wb_o: Write enable
    output logic        regfile_we_wb_o,
    
    // regfile_we_wb_power_o: Write enable for power gating
    //   - Qualified with additional conditions
    output logic        regfile_we_wb_power_o,
    
    // regfile_wdata_wb_o: Write data
    output logic [31:0] regfile_wdata_wb_o,

    // ===== Forwarding to ID Stage (ALU Port) =====
    // regfile_alu_waddr_fw_o: Destination register
    output logic [ 5:0] regfile_alu_waddr_fw_o,
    
    // regfile_alu_we_fw_o: Write enable
    output logic        regfile_alu_we_fw_o,
    
    // regfile_alu_we_fw_power_o: Write enable for power
    output logic        regfile_alu_we_fw_power_o,
    
    // regfile_alu_wdata_fw_o: Forwarded result
    //   - ALU, MULT, CSR, or APU result
    output logic [31:0] regfile_alu_wdata_fw_o,

    // ===== Branch Resolution Output to IF =====
    // jump_target_o: Branch/jump target address
    output logic [31:0] jump_target_o,
    
    // branch_decision_o: Branch taken/not taken
    output logic        branch_decision_o,

    // ===== Pipeline Stall Control =====
    // is_decoding_i: ID stage decoding instruction
    //   - Used to mask APU dependencies for invalid instructions
    input logic is_decoding_i,
    
    // lsu_ready_ex_i: LSU ready (EX part complete)
    input logic lsu_ready_ex_i,
    
    // lsu_err_i: LSU error occurred
    input logic lsu_err_i,

    // ex_ready_o: EX stage ready for new instruction
    output logic ex_ready_o,
    
    // ex_valid_o: EX stage producing valid result
    output logic ex_valid_o,
    
    // wb_ready_i: WB stage ready for new data
    input  logic wb_ready_i
);

  ///////////////////////////////////////////////////////////////////////////////
  // INTERNAL SIGNALS
  ///////////////////////////////////////////////////////////////////////////////
  
  // ALU result
  logic [                31:0] alu_result;
  
  // Multiplier result
  logic [                31:0] mult_result;
  
  // ALU comparison result (for branches)
  logic                        alu_cmp_result;

  // LSU writeback control
  logic                        regfile_we_lsu;      // LSU write enable (registered)
  logic [                 5:0] regfile_waddr_lsu;   // LSU write address (registered)

  // Writeback contention flags
  logic                        wb_contention;       // ALU port contention
  logic                        wb_contention_lsu;   // LSU port contention

  // Unit ready signals
  logic                        alu_ready;           // ALU ready
  logic                        mulh_active;         // MULH operation active
  logic                        mult_ready;          // Multiplier ready

  ///////////////////////////////////////////////////////////////////////////////
  // APU SIGNALS (FPU=1 only)
  ///////////////////////////////////////////////////////////////////////////////
  
  // APU result valid
  logic                        apu_valid;
  
  // APU destination register
  logic [                 5:0] apu_waddr;
  
  // APU result data
  logic [                31:0] apu_result;
  
  // APU stall signal
  logic                        apu_stall;
  
  // APU operation active
  logic                        apu_active;
  
  // APU operation type flags
  logic                        apu_singlecycle;     // 1-cycle operation
  logic                        apu_multicycle;      // >2-cycle operation
  
  // APU handshake (internal)
  logic                        apu_req;
  logic                        apu_gnt;

  // APU result memorization (for writeback conflicts)
  logic                        apu_rvalid_q;        // Saved result valid
  logic [                31:0] apu_result_q;        // Saved result data
  logic [APU_NUSFLAGS_CPU-1:0] apu_flags_q;         // Saved FP flags

  ///////////////////////////////////////////////////////////////////////////////
  // ALU WRITEBACK PORT MUX
  ///////////////////////////////////////////////////////////////////////////////
  // Selects between ALU/MULT/CSR/APU results for ALU writeback port
  // Priority: APU (single/multi-cycle) > ALU/MULT/CSR

  // ALU write port mux
  always_comb begin
    regfile_alu_wdata_fw_o    = '0;
    regfile_alu_waddr_fw_o    = '0;
    regfile_alu_we_fw_o       = 1'b0;
    regfile_alu_we_fw_power_o = 1'b0;
    wb_contention             = 1'b0;

    // APU single cycle operations, and multicycle operations (> 2cycles) are written back on ALU port
    if (apu_valid & (apu_singlecycle | apu_multicycle)) begin
      ///////////////////////////////////////////////////////////////////////////
      // APU Result Writeback (Single-cycle or Multi-cycle)
      ///////////////////////////////////////////////////////////////////////////
      regfile_alu_we_fw_o       = 1'b1;
      regfile_alu_we_fw_power_o = 1'b1;
      regfile_alu_waddr_fw_o    = apu_waddr;
      regfile_alu_wdata_fw_o    = apu_result;

      if (regfile_alu_we_i & ~apu_en_i) begin
        // Contention: ALU/MULT/CSR wants to write, but APU using port
        wb_contention = 1'b1;
      end
      
    end else begin
      ///////////////////////////////////////////////////////////////////////////
      // Normal ALU/MULT/CSR Writeback
      ///////////////////////////////////////////////////////////////////////////
      regfile_alu_we_fw_o = regfile_alu_we_i & ~apu_en_i;
      
      // Power-qualified write enable
      // For COREV_PULP: qualify with unit readiness
      regfile_alu_we_fw_power_o = (COREV_PULP == 0) ? regfile_alu_we_i & ~apu_en_i : 
                                                     regfile_alu_we_i & ~apu_en_i &
                                                     mult_ready & alu_ready & lsu_ready_ex_i;
      
      regfile_alu_waddr_fw_o = regfile_alu_waddr_i;
      
      // Select result source
      if (alu_en_i) regfile_alu_wdata_fw_o = alu_result;
      if (mult_en_i) regfile_alu_wdata_fw_o = mult_result;
      if (csr_access_i) regfile_alu_wdata_fw_o = csr_rdata_i;
    end
  end

  ///////////////////////////////////////////////////////////////////////////////
  // LSU WRITEBACK PORT MUX
  ///////////////////////////////////////////////////////////////////////////////
  // Selects between LSU load data and APU two-cycle results
  // Priority: LSU > APU (two-cycle)

  // LSU write port mux
  always_comb begin
    regfile_we_wb_o       = 1'b0;
    regfile_we_wb_power_o = 1'b0;
    regfile_waddr_wb_o    = regfile_waddr_lsu;
    regfile_wdata_wb_o    = lsu_rdata_i;
    wb_contention_lsu     = 1'b0;

    if (regfile_we_lsu) begin
      ///////////////////////////////////////////////////////////////////////////
      // LSU Load Writeback
      ///////////////////////////////////////////////////////////////////////////
      regfile_we_wb_o       = 1'b1;
      
      // Power-qualified: don't write on misaligned or if WB not ready
      regfile_we_wb_power_o = (COREV_PULP == 0) ? 1'b1 : ~data_misaligned_ex_i & wb_ready_i;
      
      if (apu_valid & (!apu_singlecycle & !apu_multicycle)) begin
        // Contention: APU two-cycle result wants LSU port
        wb_contention_lsu = 1'b1;
      end
      
    // APU two-cycle operations are written back on LSU port
    end else if (apu_valid & (!apu_singlecycle & !apu_multicycle)) begin
      ///////////////////////////////////////////////////////////////////////////
      // APU Two-Cycle Result Writeback
      ///////////////////////////////////////////////////////////////////////////
      regfile_we_wb_o       = 1'b1;
      regfile_we_wb_power_o = 1'b1;
      regfile_waddr_wb_o    = apu_waddr;
      regfile_wdata_wb_o    = apu_result;
    end
  end

  ///////////////////////////////////////////////////////////////////////////////
  // BRANCH HANDLING
  ///////////////////////////////////////////////////////////////////////////////
  // Branch decision and target computed in EX stage
  // Resolved here to minimize branch penalty

  // branch handling
  // branch_decision_o: Comparison result from ALU (taken/not taken)
  assign branch_decision_o = alu_cmp_result;
  
  // jump_target_o: Target address (from operand_c, calculated in ID)
  assign jump_target_o     = alu_operand_c_i;


  ///////////////////////////////////////////////////////////////////////////////
  // ALU INSTANTIATION
  ///////////////////////////////////////////////////////////////////////////////
  // Arithmetic Logic Unit
  //   - Integer operations (add, sub, shift, logic, compare)
  //   - PULP SIMD vector operations
  //   - PULP complex number operations
  //   - Single-cycle execution

  ////////////////////////////
  //     _    _    _   _    //
  //    / \  | |  | | | |   //
  //   / _ \ | |  | | | |   //
  //  / ___ \| |__| |_| |   //
  // /_/   \_\_____\___/    //
  //                        //
  ////////////////////////////

  cv32e40p_alu alu_i (
      .clk        (clk),
      .rst_n      (rst_n),
      
      // Control
      .enable_i   (alu_en_i),
      .operator_i (alu_operator_i),
      
      // Operands
      .operand_a_i(alu_operand_a_i),
      .operand_b_i(alu_operand_b_i),
      .operand_c_i(alu_operand_c_i),

      // PULP vector mode
      .vector_mode_i(alu_vec_mode_i),
      .bmask_a_i    (bmask_a_i),
      .bmask_b_i    (bmask_b_i),
      .imm_vec_ext_i(imm_vec_ext_i),

      // PULP complex operations
      .is_clpx_i   (alu_is_clpx_i),
      .clpx_shift_i(alu_clpx_shift_i),
      .is_subrot_i (alu_is_subrot_i),

      // Results
      .result_o           (alu_result),         // ALU result
      .comparison_result_o(alu_cmp_result),     // Branch comparison

      // Control
      .ready_o   (alu_ready),                   // ALU ready
      .ex_ready_i(ex_ready_o)                   // EX stage ready
  );


  ///////////////////////////////////////////////////////////////////////////////
  // MULTIPLIER INSTANTIATION
  ///////////////////////////////////////////////////////////////////////////////
  // Multiplier unit
  //   - MUL: Single-cycle 32x32→32 (lower 32 bits)
  //   - MULH/MULHSU/MULHU: Multi-cycle 32x32→64 (upper 32 bits)
  //   - PULP dot products (SIMD multiply-accumulate)
  //   - PULP complex multiply

  ////////////////////////////////////////////////////////////////
  //  __  __ _   _ _   _____ ___ ____  _     ___ _____ ____     //
  // |  \/  | | | | | |_   _|_ _|  _ \| |   |_ _| ____|  _ \    //
  // | |\/| | | | | |   | |  | || |_) | |    | ||  _| | |_) |   //
  // | |  | | |_| | |___| |  | ||  __/| |___ | || |___|  _ <    //
  // |_|  |_|\___/|_____|_| |___|_|   |_____|___|_____|_| \_\   //
  //                                                            //
  ////////////////////////////////////////////////////////////////

  cv32e40p_mult mult_i (
      .clk  (clk),
      .rst_n(rst_n),

      // Control
      .enable_i  (mult_en_i),
      .operator_i(mult_operator_i),

      // Operand configuration
      .short_subword_i(mult_sel_subword_i),     // 16x16 multiply
      .short_signed_i (mult_signed_mode_i),     // Signed/unsigned mode

      // Standard multiply operands
      .op_a_i(mult_operand_a_i),
      .op_b_i(mult_operand_b_i),
      .op_c_i(mult_operand_c_i),
      .imm_i (mult_imm_i),

      // Dot product operands (PULP)
      .dot_op_a_i  (mult_dot_op_a_i),
      .dot_op_b_i  (mult_dot_op_b_i),
      .dot_op_c_i  (mult_dot_op_c_i),
      .dot_signed_i(mult_dot_signed_i),
      
      // Complex multiply control (PULP)
      .is_clpx_i   (mult_is_clpx_i),
      .clpx_shift_i(mult_clpx_shift_i),
      .clpx_img_i  (mult_clpx_img_i),

      // Result
      .result_o(mult_result),

      // Status
      .multicycle_o (mult_multicycle_o),        // Multi-cycle operation
      .mulh_active_o(mulh_active),              // MULH in progress
      .ready_o      (mult_ready),               // Multiplier ready
      .ex_ready_i   (ex_ready_o)                // EX stage ready
  );

  ///////////////////////////////////////////////////////////////////////////////
  // APU DISPATCHER (FPU=1 only)
  ///////////////////////////////////////////////////////////////////////////////
  // Manages floating-point operation offload to external APU/FPU
  // Handles dependency tracking, latency management, result routing

  generate
    if (FPU == 1) begin : gen_apu
      ////////////////////////////////////////////////////
      //     _    ____  _   _   ____ ___ ____  ____     //
      //    / \  |  _ \| | | | |  _ \_ _/ ___||  _ \    //
      //   / _ \ | |_) | | | | | | | | |\___ \| |_) |   //
      //  / ___ \|  __/| |_| | | |_| | | ___) |  __/    //
      // /_/   \_\_|    \___/  |____/___|____/|_|       //
      //                                                //
      ////////////////////////////////////////////////////

      cv32e40p_apu_disp apu_disp_i (
          .clk_i (clk),
          .rst_ni(rst_n),

          // APU control from ID
          .enable_i   (apu_en_i),
          .apu_lat_i  (apu_lat_i),              // Operation latency
          .apu_waddr_i(apu_waddr_i),            // Destination register

          // APU control outputs
          .apu_waddr_o      (apu_waddr),        // Registered destination
          .apu_multicycle_o (apu_multicycle),   // >2 cycle operation
          .apu_singlecycle_o(apu_singlecycle),  // 1 cycle operation

          // Status
          .active_o(apu_active),                // APU operation active
          .stall_o (apu_stall),                 // APU causing stall

          // Dependency tracking
          .is_decoding_i      (is_decoding_i),
          .read_regs_i        (apu_read_regs_i),
          .read_regs_valid_i  (apu_read_regs_valid_i),
          .read_dep_o         (apu_read_dep_o),
          .read_dep_for_jalr_o(apu_read_dep_for_jalr_o),
          .write_regs_i       (apu_write_regs_i),
          .write_regs_valid_i (apu_write_regs_valid_i),
          .write_dep_o        (apu_write_dep_o),

          // Performance counters
          .perf_type_o(apu_perf_type_o),
          .perf_cont_o(apu_perf_cont_o),

          // APU interconnect handshake
          .apu_req_o   (apu_req),               // Request to APU
          .apu_gnt_i   (apu_gnt),               // Grant from APU
          
          // APU response
          .apu_rvalid_i(apu_valid)              // Result valid
      );

      // Performance counter: writeback contention
      assign apu_perf_wb_o  = wb_contention | wb_contention_lsu;
      
      // APU ready for writeback when idle or result arriving
      assign apu_ready_wb_o = ~(apu_active | apu_en_i | apu_stall) | apu_valid;

      ///////////////////////////////////////////////////////////////////////////
      // APU RESULT MEMORIZATION REGISTER
      ///////////////////////////////////////////////////////////////////////////
      // Saves multi-cycle APU result if writeback stalled
      // Prevents result loss during conflicts with LSU, MULH, or JALR
      
      ///////////////////////////////////////
      // APU result memorization Register  //
      ///////////////////////////////////////
      always_ff @(posedge clk, negedge rst_n) begin : APU_Result_Memorization
        if (~rst_n) begin
          apu_rvalid_q <= 1'b0;
          apu_result_q <= 'b0;
          apu_flags_q  <= 'b0;
        end else begin
          // Save result if APU multi-cycle result arrives but writeback stalled
          if (apu_rvalid_i && apu_multicycle &&
              (data_misaligned_i || data_misaligned_ex_i ||
               ((data_req_i || data_rvalid_i) && regfile_alu_we_i) ||
               (mulh_active && (mult_operator_i == MUL_H)) ||
               ((ctrl_transfer_insn_in_dec_i == BRANCH_JALR) &&
                regfile_alu_we_i && ~apu_read_dep_for_jalr_o))) begin
            // Stall conditions:
            //   - Misaligned LSU access
            //   - LSU operation conflicts with ALU writeback
            //   - MULH active with MUL_H operation
            //   - JALR with register dependency
            apu_rvalid_q <= 1'b1;
            apu_result_q <= apu_result_i;
            apu_flags_q  <= apu_flags_i;
          end else if (apu_rvalid_q && !(data_misaligned_i || data_misaligned_ex_i ||
                                         ((data_req_i || data_rvalid_i) && regfile_alu_we_i) ||
                                         (mulh_active && (mult_operator_i == MUL_H)) ||
                                         ((ctrl_transfer_insn_in_dec_i == BRANCH_JALR) &&
                                          regfile_alu_we_i && ~apu_read_dep_for_jalr_o))) begin
            // Clear saved result when stall conditions resolved
            apu_rvalid_q <= 1'b0;
          end
        end
      end

      ///////////////////////////////////////////////////////////////////////////
      // APU INTERFACE CONNECTIONS
      ///////////////////////////////////////////////////////////////////////////
      
      // Request to external APU
      assign apu_req_o = apu_req;
      assign apu_gnt = apu_gnt_i;
      
      // Result valid (use saved or direct)
      // Suppress if stall conditions present during multi-cycle operation
      assign apu_valid = (apu_multicycle && (data_misaligned_i || data_misaligned_ex_i ||
                                             ((data_req_i || data_rvalid_i) && regfile_alu_we_i) ||
                                             (mulh_active && (mult_operator_i == MUL_H)) ||
                                             ((ctrl_transfer_insn_in_dec_i == BRANCH_JALR) &&
                                              regfile_alu_we_i && ~apu_read_dep_for_jalr_o)))
                         ? 1'b0 : (apu_rvalid_i || apu_rvalid_q);
      
      // Pass operands and operation directly to APU
      assign apu_operands_o = apu_operands_i;
      assign apu_op_o = apu_op_i;
      
      // Result mux (saved or direct)
      assign apu_result = apu_rvalid_q ? apu_result_q : apu_result_i;
      
      // FP flags writeback
      assign fpu_fflags_we_o = apu_valid;
      assign fpu_fflags_o = apu_rvalid_q ? apu_flags_q : apu_flags_i;
      
    end else begin : gen_no_apu
      ///////////////////////////////////////////////////////////////////////////
      // NO APU/FPU CONFIGURATION
      ///////////////////////////////////////////////////////////////////////////
      // Tie off all APU signals when FPU not present
      
      // default assignements for the case when no FPU/APU is attached.
      assign apu_req_o               = '0;
      assign apu_operands_o[0]       = '0;
      assign apu_operands_o[1]       = '0;
      assign apu_operands_o[2]       = '0;
      assign apu_op_o                = '0;
      assign apu_req                 = 1'b0;
      assign apu_gnt                 = 1'b0;
      assign apu_result              = 32'b0;
      assign apu_valid               = 1'b0;
      assign apu_waddr               = 6'b0;
      assign apu_stall               = 1'b0;
      assign apu_active              = 1'b0;
      assign apu_ready_wb_o          = 1'b1;
      assign apu_perf_wb_o           = 1'b0;
      assign apu_perf_cont_o         = 1'b0;
      assign apu_perf_type_o         = 1'b0;
      assign apu_singlecycle         = 1'b0;
      assign apu_multicycle          = 1'b0;
      assign apu_read_dep_o          = 1'b0;
      assign apu_read_dep_for_jalr_o = 1'b0;
      assign apu_write_dep_o         = 1'b0;
      assign fpu_fflags_o            = '0;
      assign fpu_fflags_we_o         = '0;
    end
  endgenerate

  // APU busy status
  assign apu_busy_o = apu_active;

  ///////////////////////////////////////////////////////////////////////////////
  // EX/WB PIPELINE REGISTER
  ///////////////////////////////////////////////////////////////////////////////
  // Buffers LSU writeback control between EX and WB stages
  // Registers write enable and address for load operations

  ///////////////////////////////////////
  // EX/WB Pipeline Register           //
  ///////////////////////////////////////
  always_ff @(posedge clk, negedge rst_n) begin : EX_WB_Pipeline_Register
    if (~rst_n) begin
      regfile_waddr_lsu <= '0;
      regfile_we_lsu    <= 1'b0;
    end else begin
      if (ex_valid_o) // wb_ready_i is implied
      begin
        // Register LSU write enable (suppress on LSU error)
        regfile_we_lsu <= regfile_we_i & ~lsu_err_i;
        
        if (regfile_we_i & ~lsu_err_i) begin
          // Register destination address
          regfile_waddr_lsu <= regfile_waddr_i;
        end
      end else if (wb_ready_i) begin
        // we are ready for a new instruction, but there is none available,
        // so we just flush the current one out of the pipe
        regfile_we_lsu <= 1'b0;
      end
    end
  end

  ///////////////////////////////////////////////////////////////////////////////
  // PIPELINE READY/VALID CONTROL
  ///////////////////////////////////////////////////////////////////////////////
  // Manages pipeline flow control for EX stage
  
  // As valid always goes to the right and ready to the left, and we are able
  // to finish branches without going to the WB stage, ex_valid does not
  // depend on ex_ready.
  
  // ex_ready_o: EX ready to accept new instruction from ID
  //   Conditions:
  //     - No APU stall
  //     - ALU ready
  //     - Multiplier ready
  //     - LSU (EX part) ready
  //     - WB stage ready
  //     - No writeback contention
  //   Special case: branches bypass WB (always ready)
  assign ex_ready_o = (~apu_stall & alu_ready & mult_ready & lsu_ready_ex_i
                       & wb_ready_i & ~wb_contention) | (branch_in_ex_i);
  
  // ex_valid_o: EX producing valid output to WB
  //   Conditions:
  //     - At least one unit active (APU, ALU, MULT, CSR, LSU)
  //     - All units ready for completion
  //     - WB stage ready
  assign ex_valid_o = (apu_valid | alu_en_i | mult_en_i | csr_access_i | lsu_en_i)
                       & (alu_ready & mult_ready & lsu_ready_ex_i & wb_ready_i);

endmodule
