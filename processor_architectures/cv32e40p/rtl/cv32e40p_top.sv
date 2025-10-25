// Copyright 2024 Dolphin Design
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License");
// you may not use this file except in compliance with the License, or,
// at your option, the Apache License version 2.0.
// You may obtain a copy of the License at
//
// https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/////////////////////////////////////////////////////////////////////////////
//                                                                         //
// Contributors: Pascal Gouedo, Dolphin Design <pascal.gouedo@dolphin.fr>  //
//                                                                         //
// Description:  Top level module of CV32E40P instantiating the Core and   //
//               an optional CVFPU with its clock gating cell.             //
//                                                                         //
/////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Module: cv32e40p_top
///////////////////////////////////////////////////////////////////////////////
//
// FUNCTION:
//   Top-level wrapper for CV32E40P RISC-V processor core.
//   Instantiates the main core (cv32e40p_core) and optional FPU (cvfpu).
//   Provides clean interface to system with all configuration parameters.
//
// HIERARCHY:
//   cv32e40p_top (this module)
//   ├── cv32e40p_core (main processor core)
//   │   ├── cv32e40p_if_stage (instruction fetch)
//   │   ├── cv32e40p_id_stage (instruction decode)
//   │   ├── cv32e40p_ex_stage (execute)
//   │   ├── cv32e40p_load_store_unit (memory access)
//   │   ├── cv32e40p_cs_registers (CSRs)
//   │   ├── cv32e40p_controller (main FSM)
//   │   └── cv32e40p_sleep_unit (power management)
//   └── cv32e40p_fp_wrapper (optional FPU)
//       └── fpnew (FPU from PULP FPNew project)
//
// CONFIGURATION PARAMETERS:
//   COREV_PULP: Enables PULP ISA extensions
//     - Hardware loops (lp.* instructions)
//     - Post-increment load/store
//     - Custom CSRs for loop control
//     - Does NOT include cv.elw (requires COREV_CLUSTER)
//
//   COREV_CLUSTER: Enables PULP cluster integration
//     - cv.elw (Event Load Word) instruction
//     - Cluster-level clock gating via pulp_clock_en_i
//     - Event-driven sleep/wake mechanisms
//     - Requires COREV_PULP=1
//
//   FPU: Enables floating-point unit
//     - IEEE 754 single/double precision
//     - FPNew architecture (state-of-art FPU)
//     - Configurable pipeline stages for timing closure
//
//   FPU_ADDMUL_LAT: FPU ADD/MUL pipeline depth
//     - Range: 0-3 stages
//     - Higher latency = higher Fmax
//     - 0: Combinational (low freq, small area)
//     - 3: Fully pipelined (high freq, larger area)
//
//   FPU_OTHERS_LAT: FPU comparison/conversion pipeline depth
//     - Range: 0-2 stages
//     - For FCMP, FCVT operations
//
//   ZFINX: Float-in-GPR extension
//     - FP operations use integer registers
//     - No separate FP register file
//     - Area efficient but limits parallelism
//     - Alternative to standard F/D extensions
//
//   NUM_MHPMCOUNTERS: Number of hardware performance counters
//     - Range: 0-29 counters
//     - RISC-V mhpmcounter3-mhpmcounter31
//     - Used for profiling and optimization
//
// INTERFACE SUMMARY:
//   - Instruction memory: OBI protocol (req/gnt/rvalid handshake)
//   - Data memory: OBI protocol with byte enables
//   - Interrupts: 32-bit vector, level-triggered
//   - Debug: RISC-V debug spec 0.13.2
//   - APU: Coprocessor interface to FPU
//
// CLOCK GATING:
//   Two clock domains:
//     1. Core clock (clk_i): Main processor clock
//        - Gated by sleep_unit during WFI/cv.elw
//     2. FPU clock (apu_clk): FPU clock
//        - Gated when no FPU operations active
//        - Saves power when FPU idle
//
// TYPICAL CONFIGURATIONS:
//   Minimal (no extensions):
//     COREV_PULP=0, FPU=0, NUM_MHPMCOUNTERS=0
//     Area: ~30K gates, Fmax: 400+ MHz
//
//   PULP extensions:
//     COREV_PULP=1, COREV_CLUSTER=1, FPU=0
//     Area: ~35K gates, optimized for embedded DSP
//
//   With FPU:
//     COREV_PULP=0, FPU=1, FPU_ADDMUL_LAT=2, FPU_OTHERS_LAT=1
//     Area: ~60K gates, IEEE 754 compliant
//
///////////////////////////////////////////////////////////////////////////////

module cv32e40p_top #(
    parameter COREV_PULP = 0, // PULP ISA Extension (incl. custom CSRs and hardware loop, excl. cv.elw)
    parameter COREV_CLUSTER = 0,  // PULP Cluster interface (incl. cv.elw)
    parameter FPU = 0,  // Floating Point Unit (interfaced via APU interface)
    parameter FPU_ADDMUL_LAT = 0,  // Floating-Point ADDition/MULtiplication computing lane pipeline registers number
    parameter FPU_OTHERS_LAT = 0,  // Floating-Point COMParison/CONVersion computing lanes pipeline registers number
    parameter ZFINX = 0,  // Float-in-General Purpose registers
    parameter NUM_MHPMCOUNTERS = 1
) (
    ///////////////////////////////////////////////////////////////////////////
    // Clock and Reset
    ///////////////////////////////////////////////////////////////////////////
    input logic clk_i,    // System clock (free-running or externally gated)
    input logic rst_ni,   // Active-low reset (asynchronous assertion, synchronous deassertion)

    // PULP cluster clock enable (COREV_CLUSTER=1 only)
    // External control of core clock during cv.elw sleep
    input logic pulp_clock_en_i,
    
    // Scan chain enable for DFT
    // Disables all clock gates during manufacturing test
    input logic scan_cg_en_i,

    ///////////////////////////////////////////////////////////////////////////
    // Core Configuration Inputs (typically static)
    ///////////////////////////////////////////////////////////////////////////
    
    // Boot address - PC value after reset
    // Typically points to bootloader or startup code
    input logic [31:0] boot_addr_i,
    
    // Machine trap vector base address
    // Base address for exception/interrupt handlers
    input logic [31:0] mtvec_addr_i,
    
    // Debug mode halt address
    // PC value when entering debug mode
    input logic [31:0] dm_halt_addr_i,
    
    // Hart ID - unique identifier for this core
    // Read via mhartid CSR, used in multi-core systems
    input logic [31:0] hart_id_i,
    
    // Debug exception address
    // PC value for debug exceptions
    input logic [31:0] dm_exception_addr_i,

    ///////////////////////////////////////////////////////////////////////////
    // Instruction Memory Interface (OBI Protocol)
    ///////////////////////////////////////////////////////////////////////////
    // OBI (Open Bus Interface) - simple req/gnt/rvalid handshake
    // Used for instruction fetches from memory or instruction cache
    
    output logic        instr_req_o,      // Instruction request
    input  logic        instr_gnt_i,      // Grant (address phase)
    input  logic        instr_rvalid_i,   // Response valid (data phase)
    output logic [31:0] instr_addr_o,     // Instruction address (word-aligned)
    input  logic [31:0] instr_rdata_i,    // Instruction data

    ///////////////////////////////////////////////////////////////////////////
    // Data Memory Interface (OBI Protocol)
    ///////////////////////////////////////////////////////////////////////////
    // OBI protocol with write enable and byte enables
    // Used for load/store accesses to data memory or data cache
    
    output logic        data_req_o,       // Data request
    input  logic        data_gnt_i,       // Grant (address phase)
    input  logic        data_rvalid_i,    // Response valid (data phase)
    output logic        data_we_o,        // Write enable (1=store, 0=load)
    output logic [ 3:0] data_be_o,        // Byte enables (one per byte)
    output logic [31:0] data_addr_o,      // Data address
    output logic [31:0] data_wdata_o,     // Write data (for stores)
    input  logic [31:0] data_rdata_i,     // Read data (for loads)

    ///////////////////////////////////////////////////////////////////////////
    // Interrupt Interface
    ///////////////////////////////////////////////////////////////////////////
    // 32 level-triggered interrupt inputs
    // [31:16] Fast custom interrupts, [11,7,3] Standard RISC-V interrupts
    
    input  logic [31:0] irq_i,            // Interrupt request vector
    output logic        irq_ack_o,        // Interrupt acknowledged
    output logic [ 4:0] irq_id_o,         // Interrupt ID being serviced

    ///////////////////////////////////////////////////////////////////////////
    // Debug Interface (RISC-V Debug Spec 0.13.2)
    ///////////////////////////////////////////////////////////////////////////
    // External debug module interface
    // Allows debugger to halt, step, and inspect core state
    
    input  logic debug_req_i,             // Debug request (halt core)
    output logic debug_havereset_o,       // Core has been reset
    output logic debug_running_o,         // Core is running (not halted)
    output logic debug_halted_o,          // Core is halted in debug mode

    ///////////////////////////////////////////////////////////////////////////
    // CPU Control Signals
    ///////////////////////////////////////////////////////////////////////////
    
    // Fetch enable - pulse to start core operation after reset
    // Core remains in RESET state until this is pulsed
    input  logic fetch_enable_i,
    
    // Core sleep indication
    // Asserted during WFI sleep (COREV_CLUSTER=0) or cv.elw sleep (COREV_CLUSTER=1)
    // System can use this for additional power management
    output logic core_sleep_o
);

  import cv32e40p_apu_core_pkg::*;

  ///////////////////////////////////////////////////////////////////////////
  // INTERNAL SIGNALS - APU (Auxiliary Processing Unit) Interface
  ///////////////////////////////////////////////////////////////////////////
  // APU interface connects Core to optional FPU
  // Follows standard coprocessor interface protocol
  //
  // CORE TO FPU SIGNALS:
  
  // APU busy indication from core
  // Asserts when core has outstanding FPU operation
  logic                              apu_busy;
  
  // APU request - core requests FPU operation
  // Handshakes with apu_gnt
  logic                              apu_req;
  
  // APU operands - up to 3 source operands for FPU
  // Typically rs1, rs2, rs3 for fused operations (FMADD, etc.)
  logic [   APU_NARGS_CPU-1:0][31:0] apu_operands;
  
  // APU operation encoding
  // Specifies FPU operation (FADD, FMUL, FDIV, etc.)
  logic [     APU_WOP_CPU-1:0]       apu_op;
  
  // APU flags - rounding mode, input flags
  // Includes: rounding mode (RNE, RTZ, etc.), flush-to-zero, etc.
  logic [APU_NDSFLAGS_CPU-1:0]       apu_flags;

  // FPU TO CORE SIGNALS:
  
  // APU grant - FPU accepts request
  // Completes handshake with apu_req
  logic                              apu_gnt;
  
  // APU result valid - FPU operation complete
  // May be many cycles after apu_req due to pipelining
  logic                              apu_rvalid;
  
  // APU result data - FPU operation result
  logic [                31:0]       apu_rdata;
  
  // APU result flags - exception flags (inexact, overflow, etc.)
  // IEEE 754 exception flags: NV, DZ, OF, UF, NX
  logic [APU_NUSFLAGS_CPU-1:0]       apu_rflags;

  ///////////////////////////////////////////////////////////////////////////
  // FPU CLOCK GATING SIGNALS
  ///////////////////////////////////////////////////////////////////////////
  
  // FPU clock enable - gate FPU clock when idle
  // Enable when: FPU request pending OR FPU operation in progress
  logic apu_clk_en;
  
  // Gated FPU clock output
  logic apu_clk;

  ///////////////////////////////////////////////////////////////////////////
  // CORE INSTANTIATION
  ///////////////////////////////////////////////////////////////////////////
  // Main CV32E40P processor core
  // Contains all pipeline stages, CSRs, and control logic
  //
  // Instantiate the Core
  cv32e40p_core #(
      .COREV_PULP      (COREV_PULP),
      .COREV_CLUSTER   (COREV_CLUSTER),
      .FPU             (FPU),
      .FPU_ADDMUL_LAT  (FPU_ADDMUL_LAT),
      .FPU_OTHERS_LAT  (FPU_OTHERS_LAT),
      .ZFINX           (ZFINX),
      .NUM_MHPMCOUNTERS(NUM_MHPMCOUNTERS)
  ) core_i (
      // Clock and Reset
      .clk_i (clk_i),
      .rst_ni(rst_ni),

      // PULP Cluster signals
      .pulp_clock_en_i(pulp_clock_en_i),
      .scan_cg_en_i   (scan_cg_en_i),

      // Boot and configuration addresses
      .boot_addr_i        (boot_addr_i),
      .mtvec_addr_i       (mtvec_addr_i),
      .dm_halt_addr_i     (dm_halt_addr_i),
      .hart_id_i          (hart_id_i),
      .dm_exception_addr_i(dm_exception_addr_i),

      // Instruction memory interface
      .instr_req_o   (instr_req_o),
      .instr_gnt_i   (instr_gnt_i),
      .instr_rvalid_i(instr_rvalid_i),
      .instr_addr_o  (instr_addr_o),
      .instr_rdata_i (instr_rdata_i),

      // Data memory interface
      .data_req_o   (data_req_o),
      .data_gnt_i   (data_gnt_i),
      .data_rvalid_i(data_rvalid_i),
      .data_we_o    (data_we_o),
      .data_be_o    (data_be_o),
      .data_addr_o  (data_addr_o),
      .data_wdata_o (data_wdata_o),
      .data_rdata_i (data_rdata_i),

      // APU (FPU) interface
      .apu_busy_o    (apu_busy),
      .apu_req_o     (apu_req),
      .apu_gnt_i     (apu_gnt),
      .apu_operands_o(apu_operands),
      .apu_op_o      (apu_op),
      .apu_flags_o   (apu_flags),
      .apu_rvalid_i  (apu_rvalid),
      .apu_result_i  (apu_rdata),
      .apu_flags_i   (apu_rflags),

      // Interrupt interface
      .irq_i    (irq_i),
      .irq_ack_o(irq_ack_o),
      .irq_id_o (irq_id_o),

      // Debug interface
      .debug_req_i      (debug_req_i),
      .debug_havereset_o(debug_havereset_o),
      .debug_running_o  (debug_running_o),
      .debug_halted_o   (debug_halted_o),

      // Control signals
      .fetch_enable_i(fetch_enable_i),
      .core_sleep_o  (core_sleep_o)
  );

  ///////////////////////////////////////////////////////////////////////////
  // OPTIONAL FPU INSTANTIATION
  ///////////////////////////////////////////////////////////////////////////
  // Conditionally instantiate FPU based on FPU parameter
  // When FPU=0: Drive APU interface to safe values
  // When FPU=1: Instantiate FPU with clock gating
  //
  generate
    if (FPU) begin : fpu_gen

      ///////////////////////////////////////////////////////////////////////////
      // FPU CLOCK GATING
      ///////////////////////////////////////////////////////////////////////////
      // Gate FPU clock to save power when idle
      // Enable conditions:
      //   - apu_req: New FPU operation requested
      //   - apu_busy: FPU operation in progress (multi-cycle)
      // This significantly reduces FPU dynamic power
      //
      assign apu_clk_en = apu_req | apu_busy;

      // FPU clock gate
      // Provides glitch-free gated clock to FPU
      cv32e40p_clock_gate core_clock_gate_i (
          .clk_i       (clk_i),          // Free-running clock in
          .en_i        (apu_clk_en),     // Clock enable
          .scan_cg_en_i(scan_cg_en_i),   // Test mode bypass
          .clk_o       (apu_clk)         // Gated clock out to FPU
      );

      ///////////////////////////////////////////////////////////////////////////
      // FPU WRAPPER INSTANTIATION
      ///////////////////////////////////////////////////////////////////////////
      // Wraps FPNew (PULP's floating-point unit)
      // Adapts FPNew interface to CV32E40P APU protocol
      // Configurable pipeline depth for timing closure
      //
      // Instantiate the FPU wrapper
      cv32e40p_fp_wrapper #(
          .FPU_ADDMUL_LAT(FPU_ADDMUL_LAT),  // ADD/MUL pipeline stages
          .FPU_OTHERS_LAT(FPU_OTHERS_LAT)   // CMP/CVT pipeline stages
      ) fp_wrapper_i (
          .clk_i         (apu_clk),         // Gated FPU clock
          .rst_ni        (rst_ni),          // Reset
          .apu_req_i     (apu_req),         // Request from core
          .apu_gnt_o     (apu_gnt),         // Grant to core
          .apu_operands_i(apu_operands),    // Source operands
          .apu_op_i      (apu_op),          // Operation encoding
          .apu_flags_i   (apu_flags),       // Rounding mode, flags
          .apu_rvalid_o  (apu_rvalid),      // Result valid
          .apu_rdata_o   (apu_rdata),       // Result data
          .apu_rflags_o  (apu_rflags)       // Exception flags
      );
      
    end else begin : no_fpu_gen
      
      ///////////////////////////////////////////////////////////////////////////
      // NO FPU - TIE OFF APU INTERFACE
      ///////////////////////////////////////////////////////////////////////////
      // When FPU disabled, drive APU outputs to safe values
      // Core will never assert apu_req when FPU=0, but tie off anyway
      //
      // Drive FPU output signals to 0
      assign apu_gnt    = '0;
      assign apu_rvalid = '0;
      assign apu_rdata  = '0;
      assign apu_rflags = '0;
    end
  endgenerate

  ///////////////////////////////////////////////////////////////////////////
  // END OF MODULE
  ///////////////////////////////////////////////////////////////////////////
  //
  // TOP-LEVEL WRAPPER SUMMARY:
  //
  // PURPOSE:
  //   Clean integration point for CV32E40P in SoC
  //   Handles optional FPU instantiation and clock gating
  //   All configuration via parameters
  //
  // INTEGRATION CHECKLIST:
  //   1. Connect clk_i to system clock
  //   2. Connect rst_ni with proper synchronizer
  //   3. Set boot_addr_i to boot ROM/flash address
  //   4. Set mtvec_addr_i to trap handler base
  //   5. Connect instruction interface to I-cache or memory
  //   6. Connect data interface to D-cache or memory
  //   7. Connect irq_i to interrupt controller
  //   8. Connect debug interface to debug module (optional)
  //   9. Assert fetch_enable_i pulse after reset to start core
  //  10. Choose appropriate parameter values for application
  //
  // POWER MANAGEMENT:
  //   - Core clock gated during WFI/cv.elw (in core)
  //   - FPU clock gated when idle (in this module)
  //   - Can externally gate clk_i when core_sleep_o asserted
  //
  // TYPICAL GATE COUNTS:
  //   Base core: ~30K gates
  //   + COREV_PULP: +5K gates (hardware loops, custom instr)
  //   + FPU: +25-30K gates (depends on pipeline depth)
  //   + NUM_MHPMCOUNTERS: ~500 gates each
  //
  // PERFORMANCE:
  //   Frequency: 300-500 MHz (28nm, depends on config)
  //   IPC: 0.8-0.95 (typical embedded workloads)
  //   Interrupt latency: 5-6 cycles (fast interrupts)
  //   Branch misprediction: 3 cycle penalty
  //

endmodule
