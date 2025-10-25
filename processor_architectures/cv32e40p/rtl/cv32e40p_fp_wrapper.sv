// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Wrapper for a fpnew
// Contributor: Davide Schiavone <davide@openhwgroup.org>

///////////////////////////////////////////////////////////////////////////////
// Module: cv32e40p_fp_wrapper
///////////////////////////////////////////////////////////////////////////////
// 
// FUNCTION:
//   Wrapper connecting CV32E40P APU interface to the FPNew floating-point unit.
//   Translates APU protocol signals to FPNew's interface format.
//   Configures FPNew with appropriate pipeline depths and supported formats.
//
// FPNEW OVERVIEW:
//   FPNew (Floating-Point New) is a configurable, open-source FPU developed
//   by ETH Zurich. It supports:
//   - Multiple FP formats: FP32 (single), FP64 (double), FP16 (half), FP8
//   - RISC-V standard operations: FADD, FMUL, FDIV, FSQRT, FMA
//   - Conversions between FP and integer formats
//   - Comparisons and classifications
//   - Configurable pipeline depth for timing closure
//
// SUPPORTED FORMATS (via FPU_FEATURES):
//   - FP32 (RV32F): IEEE 754 single-precision (enabled by C_RVF)
//   - FP64 (RV32D): IEEE 754 double-precision (enabled by C_RVD)
//   - FP16 (RV16F): IEEE 754 half-precision (enabled by C_XF16)
//   - FP8: Custom 8-bit format (enabled by C_XF8)
//   - FP16ALT: Alternative half-precision (enabled by C_XF16ALT)
//   - Vector ops: Parallel FP operations (enabled by C_XFVEC)
//
// PIPELINE CONFIGURATION:
//   FPU_ADDMUL_LAT: Pipeline stages for ADD/MUL/FMA operations
//     - 0: Combinational (high area, low Fmax)
//     - 1-2: Balanced (moderate area/timing)
//     - 3+: Deep pipeline (high Fmax, higher latency)
//   
//   FPU_OTHERS_LAT: Pipeline stages for COMPARE/CONVERT operations
//     - Typically shorter than ADDMUL (simpler operations)
//     - 0-1 stages common
//
// OPERATION ENCODING (apu_op_i):
//   [APU_WOP_CPU-1]    : fpu_vec_op   - Vectorial SIMD operation
//   [APU_WOP_CPU-2]    : fpu_op_mod   - Operation modifier (e.g., negate)
//   [OP_BITS-1:0]      : fpu_op       - FPNew operation code
//
// FLAGS ENCODING (apu_flags_i):
//   [C_RM-1:0]         : fp_rnd_mode  - Rounding mode (RNE, RTZ, RDN, RUP, RMM)
//   [FP_FORMAT_BITS:0] : fpu_dst_fmt  - Destination format
//   [...]:               fpu_src_fmt  - Source format
//   [...]              : fpu_int_fmt  - Integer format (for conversions)
//
// APU PROTOCOL:
//   Request phase:
//     - Core asserts apu_req_i with operands, operation, flags
//     - FPU asserts apu_gnt_o when ready to accept (may be same cycle)
//   
//   Response phase:
//     - FPU asserts apu_rvalid_o when result ready (multi-cycle later)
//     - Core samples apu_rdata_o and apu_rflags_o
//     - No backpressure on response (core always ready)
//
// TIMING:
//   - Request to response latency: Depends on operation and pipeline depth
//   - FADD/FMUL: FPU_ADDMUL_LAT + computation delay (typically 3-6 cycles)
//   - FDIV/FSQRT: Much longer (iterative, 10-30+ cycles depending on precision)
//   - FCMP/FCVT: FPU_OTHERS_LAT + computation (typically 1-3 cycles)
//
// PARAMETERS:
//   FPU_ADDMUL_LAT - Pipeline depth for ADD/MUL/FMA (0-4 typical)
//   FPU_OTHERS_LAT - Pipeline depth for other ops (0-2 typical)
//
///////////////////////////////////////////////////////////////////////////////

module cv32e40p_fp_wrapper
  import cv32e40p_apu_core_pkg::*;
#(
    // Floating-Point ADD/MUL/FMA computing lane pipeline registers
    // Higher values improve Fmax but increase latency
    // 0 = combinational, 1-2 = balanced, 3+ = deep pipeline
    parameter FPU_ADDMUL_LAT = 0,
    
    // Floating-Point COMPARE/CONVERT computing lanes pipeline registers
    // These operations are typically faster than ADD/MUL
    // Can often use fewer pipeline stages
    parameter FPU_OTHERS_LAT = 0
) (
    // Clock and Reset
    input logic clk_i,   // Clock
    input logic rst_ni,  // Active-low reset

    // APU Side: Master port (from core to FPU)
    input  logic apu_req_i,  // Request valid (core has FP operation)
    output logic apu_gnt_o,  // Grant (FPU accepts operation)

    // Request channel (operation specification)
    // Operands: Up to 3 operands for operations like FMA (a*b + c)
    input logic [   APU_NARGS_CPU-1:0][31:0] apu_operands_i,
    
    // Operation: Encodes FPU operation type and modifiers
    input logic [     APU_WOP_CPU-1:0]       apu_op_i,
    
    // Flags: Rounding mode, source/dest formats, integer format
    input logic [APU_NDSFLAGS_CPU-1:0]       apu_flags_i,

    // Response channel (result and status)
    // Result valid (FPU has completed operation)
    output logic                        apu_rvalid_o,
    
    // Result data (FP result or converted integer)
    output logic [                31:0] apu_rdata_o,
    
    // Result flags: Exception flags (invalid, div-by-zero, overflow, underflow, inexact)
    output logic [APU_NUSFLAGS_CPU-1:0] apu_rflags_o
);


  import cv32e40p_pkg::*;
  import fpnew_pkg::*;

  ///////////////////////////////////////////////////////////////////////////////
  // Signal Unpacking and Format Conversion
  ///////////////////////////////////////////////////////////////////////////////
  // Extract FPNew-specific fields from APU interface signals
  
  // FPU operation fields (from apu_op_i)
  logic [        fpnew_pkg::OP_BITS-1:0] fpu_op;       // Operation code (ADD, MUL, DIV, etc.)
  logic                                  fpu_op_mod;   // Operation modifier (e.g., negate for FNMSUB)
  logic                                  fpu_vec_op;   // Vector/SIMD operation mode

  // Format specification fields (from apu_flags_i)
  logic [ fpnew_pkg::FP_FORMAT_BITS-1:0] fpu_dst_fmt;  // Destination FP format (FP32/FP64/FP16)
  logic [ fpnew_pkg::FP_FORMAT_BITS-1:0] fpu_src_fmt;  // Source FP format
  logic [fpnew_pkg::INT_FORMAT_BITS-1:0] fpu_int_fmt;  // Integer format (for conversions)
  logic [                      C_RM-1:0] fp_rnd_mode;  // Rounding mode



  // Unpack operation code from APU interface
  // apu_op_i format: {vec_op[1], op_mod[1], operation[OP_BITS]}
  assign {fpu_vec_op, fpu_op_mod, fpu_op} = apu_op_i;

  // Unpack format and rounding mode from APU flags
  // apu_flags_i format: {int_fmt, src_fmt, dst_fmt, rnd_mode}
  assign {fpu_int_fmt, fpu_src_fmt, fpu_dst_fmt, fp_rnd_mode} = apu_flags_i;



  ///////////////////////////////////////////////////////////////////////////////
  // FPU Configuration
  ///////////////////////////////////////////////////////////////////////////////
  // Configure FPNew features and implementation parameters
  
  // -----------
  // FPU Features (enabled formats, vectors etc.)
  // -----------
  // Defines which FP formats and features are supported
  localparam fpnew_pkg::fpu_features_t FPU_FEATURES = '{
      // Data path width (32-bit for CV32E40P)
      Width: C_FLEN,
      
      // Enable vectorial SIMD operations (parallel FP ops)
      EnableVectors: C_XFVEC,
      
      // NaN boxing: Disabled (not needed for RV32)
      // (RV64 with 32-bit FP ops requires NaN boxing in upper bits)
      EnableNanBox: 1'b0,
      
      // Floating-point format mask: Which FP formats are implemented
      // [FP32, FP64, FP16, FP8, FP16ALT]
      FpFmtMask: {C_RVF, C_RVD, C_XF16, C_XF8, C_XF16ALT},
      
      // Integer format mask: Which integer widths supported for conversions
      // [INT8, INT16, INT32, INT64]
      // INT8/16 only for vector mode, INT32 always, INT64 not supported in RV32
      IntFmtMask: {C_XFVEC && C_XF8, C_XFVEC && (C_XF16 || C_XF16ALT), 1'b1, 1'b0}
  };

  // -----------
  // FPU Implementation (pipeline registers configuration)
  // -----------
  // Defines how many pipeline stages each operation unit has
  localparam fpnew_pkg::fpu_implementation_t FPU_IMPLEMENTATION = '{
      // Pipeline register stages per format: [FP32, FP64, FP16, FP8, FP16alt]
      PipeRegs: '{
          // ADDMUL unit: ADD, MUL, FMA operations
          '{FPU_ADDMUL_LAT, C_LAT_FP64, C_LAT_FP16, C_LAT_FP8, C_LAT_FP16ALT},
          
          // DIVSQRT unit: DIV and SQRT operations (typically iterative)
          '{default: C_LAT_DIVSQRT},
          
          // NONCOMP unit: Comparisons, min/max, sign injection
          '{default: FPU_OTHERS_LAT},
          
          // CONV unit: Format conversions and FP<->INT conversions
          '{default: FPU_OTHERS_LAT}
      },
      
      // Unit types: How operations are grouped
      UnitTypes: '{
          '{default: fpnew_pkg::MERGED},    // ADDMUL: Merged unit (shared resources)
          '{default: fpnew_pkg::MERGED},    // DIVSQRT: Merged unit
          '{default: fpnew_pkg::PARALLEL},  // NONCOMP: Parallel units (faster)
          '{default: fpnew_pkg::MERGED}     // CONV: Merged unit
      },
      
      // Pipeline config: Where to place registers (BEFORE, AFTER, INSIDE, DISTRIBUTED)
      // AFTER: Registers at output of each stage (simpler, better for timing)
      PipeConfig: fpnew_pkg::AFTER
  };

  ///////////////////////////////////////////////////////////////////////////////
  // FPU Instance
  ///////////////////////////////////////////////////////////////////////////////
  // Instantiate FPNew top-level module with CV32E40P configuration
  
  //---------------
  // FPU instance
  //---------------

  fpnew_top #(
      .Features      (FPU_FEATURES),      // Enable features (formats, vectors)
      .Implementation(FPU_IMPLEMENTATION), // Pipeline configuration
      .PulpDivsqrt   (1'b0),              // Use standard iterative div/sqrt (not PULP optimized)
      .TagType       (logic)              // Tag type for tracking (unused here)
  ) i_fpnew_bulk (
      // Clock and reset
      .clk_i         (clk_i),
      .rst_ni        (rst_ni),
      
      // Input operands (up to 3 for FMA)
      .operands_i    (apu_operands_i),
      
      // Rounding mode
      .rnd_mode_i    (fpnew_pkg::roundmode_e'(fp_rnd_mode)),
      
      // Operation specification
      .op_i          (fpnew_pkg::operation_e'(fpu_op)),      // Operation type
      .op_mod_i      (fpu_op_mod),                           // Operation modifier
      .src_fmt_i     (fpnew_pkg::fp_format_e'(fpu_src_fmt)), // Source format
      .dst_fmt_i     (fpnew_pkg::fp_format_e'(fpu_dst_fmt)), // Destination format
      .int_fmt_i     (fpnew_pkg::int_format_e'(fpu_int_fmt)),// Integer format
      .vectorial_op_i(fpu_vec_op),                           // Vector operation
      .tag_i         (1'b0),                                 // Tag (unused)
      .simd_mask_i   (1'b0),                                 // SIMD mask (unused)
      
      // Input handshake
      .in_valid_i    (apu_req_i),  // Request valid
      .in_ready_o    (apu_gnt_o),  // Ready to accept (grant)
      
      // Flush signal (not used in CV32E40P)
      .flush_i       (1'b0),
      
      // Output result
      .result_o      (apu_rdata_o),   // FP result
      .status_o      (apu_rflags_o),  // Exception flags
      .tag_o         (  /* unused */),// Tag output (unused)
      
      // Output handshake
      .out_valid_o   (apu_rvalid_o),  // Result valid
      .out_ready_i   (1'b1),          // Always ready (no backpressure)
      
      // Busy signal (not used)
      .busy_o        (  /* unused */)
  );

  ///////////////////////////////////////////////////////////////////////////////
  // Implementation Notes
  ///////////////////////////////////////////////////////////////////////////////
  // ALTERNATIVE IMPLEMENTATION: Dedicated FPU
  // Instead of using generic FPNew, could implement custom FPU:
  //   - Optimize for specific formats (e.g., FP32 only)
  //   - Reduce area by removing unused features
  //   - Simplify control logic for fixed pipeline depth
  // Trade-off: Lower area/power vs loss of flexibility
  //
  // ALTERNATIVE IMPLEMENTATION: Shared FPU
  // For multi-core systems, could share one FPU across cores:
  //   - Add arbitration logic for multiple APU masters
  //   - Tag transactions to route results back to correct core
  //   - Reduces total area but increases latency/contention
  // Trade-off: Area savings vs performance in parallel workloads
  //
  // PERFORMANCE OPTIMIZATION: Fused Multiply-Add
  // FMA (a*b + c) is critical for many algorithms:
  //   - Single rounding (vs two for separate MUL+ADD)
  //   - Higher precision intermediate result
  //   - Lower latency than separate operations
  // FPNew implements true FMA with single rounding point
  //
  // TIMING OPTIMIZATION: Pipeline Depth Selection
  // Guidelines for FPU_ADDMUL_LAT:
  //   - 0 stages: <200 MHz, minimal area, ~5ns critical path
  //   - 1 stage:  200-400 MHz, balanced, ~2.5ns critical path
  //   - 2 stages: 400-600 MHz, higher area, ~1.7ns critical path
  //   - 3+ stages: >600 MHz, significant area, best for HPC
  // Select based on target frequency and area budget
  //
  // VERIFICATION: FP Operations
  // Floating-point correctness requires extensive testing:
  //   - Rounding mode corner cases (RNE, RTZ, RDN, RUP, RMM)
  //   - Special values (NaN, Inf, denormals, signed zero)
  //   - Exception flag generation (invalid, overflow, underflow, inexact)
  //   - Format conversion edge cases
  // Use Berkeley TestFloat or similar test suites

endmodule  // cv32e40p_fp_wrapper
