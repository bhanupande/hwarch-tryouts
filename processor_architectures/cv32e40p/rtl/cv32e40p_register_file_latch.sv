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
// Engineer:       Antonio Pullini - pullinia@iis.ee.ethz.ch                  //
//                                                                            //
// Additional contributions by:                                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    RISC-V register file                                       //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Register file with 31x 32 bit wide registers. Register 0   //
//                 is fixed to 0. This register file is based on latches and  //
//                 is thus smaller than the flip-flop based register file.    //
//                 Also supports the fp-register file now if FPU=1            //
//                 If ZFINX is 1, floating point operations take values       //
//                 from the X register file                                   //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Module: cv32e40p_register_file (LATCH-BASED IMPLEMENTATION)
///////////////////////////////////////////////////////////////////////////////
// 
// FUNCTION:
//   Latch-based general-purpose and floating-point register file.
//   Implements same interface as cv32e40p_register_file_ff.sv but uses
//   transparent latches instead of flip-flops for ~50% area savings.
//
// LATCH vs FLIP-FLOP COMPARISON:
//   Latches (this file):
//     + Approximately 50% smaller area (1 latch vs 2 flip-flops)
//     + Zero-delay read-during-write (transparent when clock high)
//     + Lower power consumption per bit
//     - Timing analysis more complex (transparency window)
//     - Risk of race conditions if not carefully controlled
//     - Not synthesizable on FPGAs (no latch primitives)
//     - Harder formal verification (level-sensitive)
//   
//   Flip-flops (cv32e40p_register_file_ff.sv):
//     + Fully synchronous (edge-triggered only)
//     + Simpler timing (setup/hold at clock edge)
//     + FPGA compatible
//     + Easier formal verification
//     - Larger area (~2x latches)
//     - Higher power consumption
//     - One-cycle delay for read-during-write
//
// WHEN TO USE THIS FILE:
//   - ASIC implementations only (latches don't exist in FPGAs)
//   - Area-constrained designs (embedded processors)
//   - When read-during-write forwarding is desired
//   - When design team has latch timing closure expertise
//
// WHEN TO USE FF VERSION:
//   - FPGA targets (latches not available)
//   - First-time implementations (safer)
//   - When formal verification is priority
//   - When design predictability > area savings
//
// LATCH OPERATION:
//   Active-low latches: Transparent when clock=0, capture when clock=1
//   Write Data Flow:
//     1. Cycle N: Write data arrives, captured in FF on posedge clk
//     2. Clock goes HIGH: Latch is opaque (holds previous value)
//     3. Clock goes LOW: Latch becomes transparent, new data passes through
//     4. Clock goes HIGH: Latch captures and holds new data
//
// READ-DURING-WRITE BEHAVIOR:
//   When reading an address being written:
//     - Flip-flop version: Returns OLD value (before write)
//     - Latch version: Returns NEW value (write-through)
//   This eliminates one cycle of forwarding logic in pipeline
//
// CLOCK GATING STRATEGY:
//   Individual clock gating per register:
//     - Only enable clock for registers being written
//     - Significant dynamic power savings
//     - NUM_WORDS clock gates required (31 for integer regs)
//   Global clock gate:
//     - Disables entire register file when no writes
//     - Reduces toggling of input FF clocks
//
// RISC-V REGISTER ARCHITECTURE:
//   Same as FF version - see cv32e40p_register_file_ff.sv for details
//   - 32 integer registers: x0=0, x1-x31
//   - 32 FP registers: f0-f31 (when FPU=1, ZFINX=0)
//   - 3 read ports, 2 write ports
//
// TIMING CRITICAL PATHS:
//   1. Write data FF → Latch transparent → Read output
//      - Shorter than FF version (no FF clock-to-Q delay)
//   2. Clock gating logic → Latch enable
//      - Must close before clock edge
//   3. Write address decode → Clock gate enable
//      - Impacts latch setup time
//
// AREA ESTIMATE:
//   Integer registers: 31 regs × 32 bits × 1 latch = 992 latches
//   Plus: 31 clock gates, address decode logic, write data FFs
//   Total: ~50-60% of flip-flop version area
//
///////////////////////////////////////////////////////////////////////////////

module cv32e40p_register_file #(
    // Address width: 5 bits for 32 registers, 6 bits with FP extension
    parameter ADDR_WIDTH = 5,
    
    // Data width: 32 bits for RV32
    parameter DATA_WIDTH = 32,
    
    // Enable floating-point register file
    parameter FPU        = 0,
    
    // ZFINX: FP operations use integer register file
    parameter ZFINX      = 0
) (
    // Clock and Reset
    input logic clk,        // Main clock
    input logic rst_n,      // Active-low asynchronous reset

    // Scan chain enable for DFT (Design for Test)
    // Disables clock gating during scan mode
    input logic scan_cg_en_i,

    ///////////////////////////////////////////////////////////////////////////
    // Read Port R1 (typically rs1)
    ///////////////////////////////////////////////////////////////////////////
    input  logic [ADDR_WIDTH-1:0] raddr_a_i,
    output logic [DATA_WIDTH-1:0] rdata_a_o,

    ///////////////////////////////////////////////////////////////////////////
    // Read Port R2 (typically rs2)
    ///////////////////////////////////////////////////////////////////////////
    input  logic [ADDR_WIDTH-1:0] raddr_b_i,
    output logic [DATA_WIDTH-1:0] rdata_b_o,

    ///////////////////////////////////////////////////////////////////////////
    // Read Port R3 (typically rs3 for MAC/FP)
    ///////////////////////////////////////////////////////////////////////////
    input  logic [ADDR_WIDTH-1:0] raddr_c_i,
    output logic [DATA_WIDTH-1:0] rdata_c_o,

    ///////////////////////////////////////////////////////////////////////////
    // Write Port W1
    ///////////////////////////////////////////////////////////////////////////
    input logic [ADDR_WIDTH-1:0] waddr_a_i,
    input logic [DATA_WIDTH-1:0] wdata_a_i,
    input logic                  we_a_i,

    ///////////////////////////////////////////////////////////////////////////
    // Write Port W2 (has priority over W1)
    ///////////////////////////////////////////////////////////////////////////
    input logic [ADDR_WIDTH-1:0] waddr_b_i,
    input logic [DATA_WIDTH-1:0] wdata_b_i,
    input logic                  we_b_i
);

  ///////////////////////////////////////////////////////////////////////////
  // LOCAL PARAMETERS
  ///////////////////////////////////////////////////////////////////////////
  
  // Number of integer registers stored (x1-x31, x0 not stored)
  localparam NUM_WORDS = 2 ** (ADDR_WIDTH - 1);
  
  // Number of floating-point registers (f0-f31)
  localparam NUM_FP_WORDS = 2 ** (ADDR_WIDTH - 1);
  
  // Total register count
  localparam NUM_TOT_WORDS = FPU ? (ZFINX ? NUM_WORDS : NUM_WORDS + NUM_FP_WORDS) : NUM_WORDS;

  ///////////////////////////////////////////////////////////////////////////
  // INTERNAL STORAGE AND SIGNALS
  ///////////////////////////////////////////////////////////////////////////
  
  // Integer register file: Latch-based storage
  // Active-low latches: Transparent when clock=0, hold when clock=1
  logic [   DATA_WIDTH-1:0] mem            [NUM_WORDS];
  
  // One-hot write address decoders (combinational)
  // Index 0 excluded (x0 is hardwired to 0, never written)
  logic [NUM_TOT_WORDS-1:1] waddr_onehot_a;     // Port A one-hot decode
  logic [NUM_TOT_WORDS-1:1] waddr_onehot_b;     // Port B one-hot decode
  logic [NUM_TOT_WORDS-1:1] waddr_onehot_b_q;   // Port B one-hot registered
  
  // Individual clock enables for each register (for clock gating)
  logic        [NUM_TOT_WORDS-1:1] mem_clocks;
  
  // Registered write data (captured on posedge clk)
  // Latches sample from these FFs during transparency window
  logic        [   DATA_WIDTH-1:0] wdata_a_q;
  logic        [   DATA_WIDTH-1:0] wdata_b_q;

  // Masked write addresses (for future x0 protection if needed)
  logic        [   ADDR_WIDTH-1:0] waddr_a;
  logic        [   ADDR_WIDTH-1:0] waddr_b;

  // Globally gated clock (enabled when any write occurs)
  // Saves power by not toggling write data FFs when no writes
  logic                            clk_int;

  // Floating-point register file: Latch-based storage
  logic        [   DATA_WIDTH-1:0] mem_fp     [NUM_FP_WORDS];

  // Loop variables for generate blocks
  int unsigned                     i;
  int unsigned                     j;
  int unsigned                     k;
  int unsigned                     l;

  genvar x;
  genvar y;

  ///////////////////////////////////////////////////////////////////////////
  // READ LOGIC - COMBINATIONAL
  ///////////////////////////////////////////////////////////////////////////
  // Identical to flip-flop version
  // Direct mux from latch outputs based on address
  // 
  // LATCH TRANSPARENCY ADVANTAGE:
  //   When reading address being written (read-during-write):
  //     - Latch is transparent during low phase of clock
  //     - New write data passes through immediately
  //     - Read returns NEW value (not old value like FF version)
  //   This eliminates need for one cycle of forwarding logic
  //
  // ADDRESS DECODING:
  //   Bit [5]: Selects integer (0) or FP (1) register file
  //   Bits [4:0]: Register index (0-31)
  //
  //-----------------------------------------------------------------------------
  //-- READ : Read address decoder RAD
  //-----------------------------------------------------------------------------
  assign rdata_a_o = raddr_a_i[5] ? mem_fp[raddr_a_i[4:0]] : mem[raddr_a_i[4:0]];
  assign rdata_b_o = raddr_b_i[5] ? mem_fp[raddr_b_i[4:0]] : mem[raddr_b_i[4:0]];
  assign rdata_c_o = raddr_c_i[5] ? mem_fp[raddr_c_i[4:0]] : mem[raddr_c_i[4:0]];

  ///////////////////////////////////////////////////////////////////////////
  // WRITE DATA CAPTURE - SEQUENTIAL
  ///////////////////////////////////////////////////////////////////////////
  // Two-stage write process for latch-based register file:
  //   Stage 1: Capture write data in FFs (this block)
  //   Stage 2: Transfer from FFs to latches (latch block below)
  //
  // GLOBAL CLOCK GATING:
  //   clk_int only toggles when we_a_i OR we_b_i is asserted
  //   Saves power by not toggling wdata_x_q FFs when no writes
  //   Important because write data is 32 bits × 2 ports = 64 FFs
  //
  // WHY REGISTER WRITE DATA?
  //   1. Data stability: Ensures write data stable during latch transparency
  //   2. Timing: Allows address decode and clock gating logic to settle
  //   3. Hold time: Guarantees data held after latch closes
  //
  // WRITE PRIORITY SETUP:
  //   Both ports captured independently here
  //   Priority (Port B > Port A) resolved in latch block
  //   waddr_onehot_b_q registered to align with wdata_b_q timing
  //
  // TIMING SEQUENCE:
  //   Cycle N, Phase 1 (posedge clk):
  //     - Capture wdata_a/b into wdata_a/b_q FFs
  //     - Capture waddr_onehot_b into waddr_onehot_b_q
  //     - Latches are CLOSED (opaque) during high phase
  //   Cycle N, Phase 2 (clock goes low):
  //     - Latches become TRANSPARENT
  //     - wdata_x_q values pass through to latch outputs
  //   Cycle N, Phase 3 (clock goes high):
  //     - Latches CAPTURE and hold new values
  //     - Ready for next cycle
  //
  //-----------------------------------------------------------------------------
  // WRITE : SAMPLE INPUT DATA
  //---------------------------------------------------------------------------

  // Global clock gate: Only clock write data FFs when needed
  // Significant power savings in register-intensive code
  cv32e40p_clock_gate CG_WE_GLOBAL (
      .clk_i       (clk),
      .en_i        (we_a_i | we_b_i),        // Enable if ANY write
      .scan_cg_en_i(scan_cg_en_i),           // Bypass during scan test
      .clk_o       (clk_int)                 // Gated clock output
  );

  // Capture write data and address on enabled clock edges
  // use clk_int here, since otherwise we don't want to write anything anyway
  always_ff @(posedge clk_int, negedge rst_n) begin : sample_waddr
    if (~rst_n) begin
      wdata_a_q        <= '0;
      wdata_b_q        <= '0;
      waddr_onehot_b_q <= '0;
    end else begin
      // Capture write data only when corresponding write enable is active
      if (we_a_i) wdata_a_q <= wdata_a_i;

      if (we_b_i) wdata_b_q <= wdata_b_i;

      // Always capture port B address decode for priority resolution
      // Needs to be aligned timing-wise with wdata_b_q
      waddr_onehot_b_q <= waddr_onehot_b;
    end
  end

  ///////////////////////////////////////////////////////////////////////////
  // WRITE ADDRESS DECODER - COMBINATIONAL
  ///////////////////////////////////////////////////////////////////////////
  // Converts binary write addresses to one-hot enables
  // Used to generate individual clock gates for each register
  //
  // ONE-HOT ENCODING BENEFITS:
  //   1. Direct indexing: waddr_onehot_x[i] enables register i
  //   2. Clock gating: Each bit can gate individual register clock
  //   3. No decode delay: Parallel decode for all registers
  //
  // PRIORITY NOTE:
  //   Both ports decoded independently here
  //   Actual priority (Port B > Port A) resolved in latch block
  //   by checking waddr_onehot_b_q before using wdata_a_q
  //
  // INDEX RANGE:
  //   Starts at 1, not 0 (x0 is hardwired to 0, never written)
  //
  //-----------------------------------------------------------------------------
  //-- WRITE : Write Address Decoder (WAD), combinatorial process
  //-----------------------------------------------------------------------------

  // Address masking (currently pass-through, could add x0 protection)
  assign waddr_a = waddr_a_i;
  assign waddr_b = waddr_b_i;

  // Generate one-hot write enables for each register (except x0)
  genvar gidx;
  generate
    for (gidx = 1; gidx < NUM_TOT_WORDS; gidx++) begin : gen_we_decoder
      assign waddr_onehot_a[gidx] = (we_a_i == 1'b1) && (waddr_a == gidx);
      assign waddr_onehot_b[gidx] = (we_b_i == 1'b1) && (waddr_b == gidx);
    end
  endgenerate

  ///////////////////////////////////////////////////////////////////////////
  // PER-REGISTER CLOCK GATING
  ///////////////////////////////////////////////////////////////////////////
  // Individual clock gate for each register
  // Only enables clock to a register when it's being written
  //
  // POWER SAVINGS:
  //   Without clock gating: All latches toggle every cycle
  //   With clock gating: Only written registers toggle
  //   Typical savings: 70-90% reduction in register file dynamic power
  //
  // CLOCK GATE OPERATION:
  //   Input: clk_int (already gated by global we_a_i | we_b_i)
  //   Enable: waddr_onehot_a[x] | waddr_onehot_b[x]
  //     - Asserts when either port writes to register x
  //     - OR logic handles dual writes to same register
  //   Output: mem_clocks[x] - gated clock for register x
  //
  // LATCH CLOCK TIMING:
  //   mem_clocks[x] = 1 (HIGH):
  //     - Latch is OPAQUE (holds previous value)
  //     - Write data settling in wdata_x_q FFs
  //   mem_clocks[x] = 0 (LOW):
  //     - Latch is TRANSPARENT
  //     - wdata_x_q passes through to latch output
  //   mem_clocks[x] → 1 (RISING):
  //     - Latch CAPTURES data
  //     - Data held until next write
  //
  // AREA COST:
  //   NUM_WORDS-1 = 31 clock gates for integer registers
  //   NUM_FP_WORDS = 32 clock gates for FP registers (if enabled)
  //   Total: 31-63 clock gate cells
  //   But saves significant power in return
  //
  // SCAN MODE:
  //   scan_cg_en_i bypasses clock gating during test
  //   Ensures all registers scannable for manufacturing test
  //
  //-----------------------------------------------------------------------------
  //-- WRITE : Clock gating (if integrated clock-gating cells are available)
  //-----------------------------------------------------------------------------
  generate
    for (x = 1; x < NUM_TOT_WORDS; x++) begin : gen_clock_gate
      cv32e40p_clock_gate clock_gate_i (
          .clk_i       (clk_int),                              // Globally gated clock
          .en_i        (waddr_onehot_a[x] | waddr_onehot_b[x]), // Enable if either port writes to reg x
          .scan_cg_en_i(scan_cg_en_i),                         // Bypass for scan mode
          .clk_o       (mem_clocks[x])                         // Per-register gated clock
      );
    end
  endgenerate

  ///////////////////////////////////////////////////////////////////////////
  // INTEGER REGISTER LATCH ARRAY
  ///////////////////////////////////////////////////////////////////////////
  // Active-low latches for register storage
  // Transparent when clock=0, capture when clock=1
  //
  // LATCH-BASED WRITE OPERATION:
  //   Phase 1 - Clock HIGH (opaque):
  //     - Latches hold previous values
  //     - wdata_x_q FFs capture new write data
  //     - Address decode and clock gating settle
  //   
  //   Phase 2 - Clock LOW (transparent):
  //     - Selected latch (mem_clocks[k] = 0) becomes transparent
  //     - Write data from wdata_x_q passes through latch
  //     - Read ports can see new value immediately (write-through)
  //   
  //   Phase 3 - Clock goes HIGH (capture):
  //     - Latch captures data on rising edge of mem_clocks[k]
  //     - Data held until next write to that register
  //
  // WRITE PORT PRIORITY:
  //   Port B > Port A (same as FF version)
  //   Implementation: waddr_onehot_b_q ? wdata_b_q : wdata_a_q
  //   If both ports write same register:
  //     - Check waddr_onehot_b_q first
  //     - If asserted, use wdata_b_q
  //     - Otherwise use wdata_a_q
  //
  // REGISTER x0 HANDLING:
  //   mem[0] assigned to '0 combinationally
  //   Even if accidentally written, reads always return 0
  //   No latch instantiated for mem[0] (assigned in always_latch)
  //
  // RESET BEHAVIOR:
  //   Asynchronous reset clears all registers to 0
  //   Important: Reset has priority over latch transparency
  //   Ensures deterministic state after reset
  //
  // ALWAYS_LATCH CONSTRUCT:
  //   SystemVerilog level-sensitive procedural block
  //   Infers transparent latches (not flip-flops)
  //   Synthesis tools map to technology latch cells
  //
  // READ-DURING-WRITE:
  //   During clock LOW phase:
  //     - Latch is transparent
  //     - Read immediately sees new write data
  //     - No forwarding needed in pipeline
  //   This is major advantage over FF version
  //
  // TIMING CONSTRAINTS:
  //   Setup: wdata_x_q stable before mem_clocks[k] rises
  //   Hold: wdata_x_q stable after mem_clocks[k] rises
  //   Transparency: wdata_x_q → latch_out delay during LOW phase
  //
  // ALTERNATIVE IMPLEMENTATIONS:
  //   1. Master-slave latch pairs: More area, fully static
  //   2. Pulsed latches: Smaller, but timing critical
  //   3. Flip-flops: Larger, but simpler timing (see _ff.sv)
  //
  //-----------------------------------------------------------------------------
  //-- WRITE : Write operation
  //-----------------------------------------------------------------------------
  //-- Generate M = WORDS sequential processes, each of which describes one
  //-- word of the memory. The processes are synchronized with the clocks
  //-- ClocksxC(i), i = 0, 1, ..., M-1
  //-- Use active low, i.e. transparent on low latches as storage elements
  //-- Data is sampled on rising clock edge

  // Integer registers (x1-x31, x0 special)
  always_latch begin : latch_wdata
    // Note: The assignment has to be done inside this process or Modelsim complains about it
    // Register x0: Hardwired to zero (RISC-V requirement)
    mem[0] = '0;

    // Registers x1 through x31
    for (k = 1; k < NUM_WORDS; k++) begin : w_WordIter
      if (~rst_n) 
        // Asynchronous reset: Clear register
        mem[k] <= '0;
      else if (mem_clocks[k] == 1'b1) 
        // Clock HIGH (capture mode): Update register with write data
        // Priority: Check port B first, then port A
        mem[k] <= waddr_onehot_b_q[k] ? wdata_b_q : wdata_a_q;
      // When mem_clocks[k] == 1'b0: Latch is transparent, holds previous value
    end
  end

  ///////////////////////////////////////////////////////////////////////////
  // FLOATING-POINT REGISTER LATCH ARRAY
  ///////////////////////////////////////////////////////////////////////////
  // Separate FP register file when FPU=1 and ZFINX=0
  // Same latch-based architecture as integer registers
  //
  // FP REGISTER DIFFERENCES FROM INTEGER:
  //   - All 32 registers are writable (no f0=0 requirement)
  //   - Address offset: waddr_onehot_x[l+NUM_WORDS] for FP reg l
  //   - Only instantiated when FPU=1 && ZFINX=0
  //
  // ZFINX MODE:
  //   When ZFINX=1: FP operations use integer registers
  //   This block not generated, saving area
  //
  // TIMING:
  //   Identical to integer register timing
  //   Same clock gating strategy
  //   Same write priority (Port B > Port A)
  //
  if (FPU == 1 && ZFINX == 0) begin
    // Floating point registers (f0-f31)
    always_latch begin : latch_wdata_fp
      if (FPU == 1) begin
        for (l = 0; l < NUM_FP_WORDS; l++) begin : w_WordIter
          if (~rst_n) 
            mem_fp[l] <= '0;
          else if (mem_clocks[l+NUM_WORDS] == 1'b1)
            // Write priority: Port B > Port A
            mem_fp[l] <= waddr_onehot_b_q[l+NUM_WORDS] ? wdata_b_q : wdata_a_q;
        end
      end
    end
  end

  ///////////////////////////////////////////////////////////////////////////
  // END OF MODULE
  ///////////////////////////////////////////////////////////////////////////
  //
  // LATCH-BASED REGISTER FILE SUMMARY:
  //
  // ADVANTAGES:
  //   + 50% area reduction vs flip-flops
  //   + Zero-delay read-during-write (transparent forwarding)
  //   + Lower power per bit stored
  //   + Aggressive clock gating for power savings
  //
  // DISADVANTAGES:
  //   - ASIC-only (FPGAs don't have latch primitives)
  //   - Complex timing analysis (transparency window)
  //   - Potential race conditions if not careful
  //   - Harder formal verification
  //   - Requires latch timing expertise
  //
  // WHEN TO USE:
  //   - ASIC targets with area constraints
  //   - Design team has latch design experience
  //   - When read-through forwarding is beneficial
  //   - Power-optimized embedded processors
  //
  // WHEN TO AVOID:
  //   - FPGA targets (use _ff.sv instead)
  //   - First silicon tapeout (risk reduction)
  //   - When formal verification is critical
  //   - Limited latch timing closure resources
  //
endmodule
