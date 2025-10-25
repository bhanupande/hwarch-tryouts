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
// Engineer:       Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    hwloop regs                                                //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Hardware loop registers                                    //
//                 a) store start/end address of N=4 hardware loops           //
//                 b) store init value of counter for each hardware loop      //
//                 c) decrement counter if hwloop taken                       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Module: cv32e40p_hwloop_regs
///////////////////////////////////////////////////////////////////////////////
// 
// FUNCTION:
//   Register file for hardware loop control (PULP ISA extension).
//   Stores loop parameters for zero-overhead loops without software overhead.
//   Each loop has three registers: START, END, COUNT.
//
// HARDWARE LOOP CONCEPT:
//   Traditional software loops require:
//     1. Compare counter to limit (1 instruction)
//     2. Conditional branch back to start (1 instruction)
//     3. Decrement counter (1 instruction)
//   Total: 3 instructions per iteration, plus pipeline stalls
//
//   Hardware loops eliminate this overhead:
//     - Controller automatically detects when PC reaches END address
//     - Counter decremented automatically
//     - Zero-cycle jump back to START address
//     - No branch prediction needed (perfect prediction)
//   Total: 0 instructions per iteration for loop control
//
// LOOP SEMANTICS:
//   When PC == END address and counter > 0:
//     1. Decrement counter
//     2. Jump to START address (zero latency)
//   When PC == END address and counter == 0:
//     1. Exit loop (continue to PC+4 or next compressed instruction)
//
// REGISTER STRUCTURE (per loop):
//   hwlp_start[i] - Loop start address (aligned to 4 bytes, [1:0] forced to 0)
//   hwlp_end[i]   - Loop end address (last instruction, aligned to 4 bytes)
//   hwlp_counter[i] - Iteration count (decrements on each loop)
//
// NESTED LOOP SUPPORT:
//   With N_REGS=2, supports 2 levels of loop nesting:
//     - Loop 0 (outer): larger iteration space
//     - Loop 1 (inner): executes multiple times per outer iteration
//   Controller determines loop priority (inner loops checked first)
//
// CSR INTERFACE:
//   Loops configured via CSR writes (from EX stage):
//     - hwlp_we_i[0]: Write START address
//     - hwlp_we_i[1]: Write END address
//     - hwlp_we_i[2]: Write COUNTER value
//     - hwlp_regid_i: Selects which loop register set (0 or 1)
//
// ADDRESS ALIGNMENT:
//   START and END addresses forced to word-aligned (bits [1:0] = 2'b00)
//   Compressed instructions within loop are supported via aligner
//
// TIMING:
//   - Counter decrement: Combinational (hwlp_counter_n = hwlp_counter_q - 1)
//   - Register update: Sequential (on clock edge)
//   - Critical path: Decrement request → counter comparison → loop decision
//
// PERFORMANCE IMPACT:
//   Example: 1000-iteration loop
//     - Software: 3000 extra instructions + branch penalty
//     - Hardware: 0 extra instructions, perfect prediction
//     - Speedup: ~3-4x for loop-intensive code
//
// PARAMETERS:
//   N_REGS     - Number of hardware loop register sets (typically 2)
//   N_REG_BITS - Address width for loop selection (log2(N_REGS))
//
// INTERFACE:
//   Write path (from EX stage):
//     hwlp_start_data_i - Loop start address to write
//     hwlp_end_data_i   - Loop end address to write
//     hwlp_cnt_data_i   - Loop counter value to write
//     hwlp_we_i[2:0]    - Write enables [2]=counter, [1]=end, [0]=start
//     hwlp_regid_i      - Loop register set selector (0 to N_REGS-1)
//   
//   Control path (from controller):
//     valid_i           - Instruction valid (gate counter decrement)
//     hwlp_dec_cnt_i    - Decrement counter for each loop (from controller)
//   
//   Read path (to controller):
//     hwlp_start_addr_o - Loop start addresses for all loops
//     hwlp_end_addr_o   - Loop end addresses for all loops
//     hwlp_counter_o    - Loop counters for all loops
//
///////////////////////////////////////////////////////////////////////////////

module cv32e40p_hwloop_regs #(
    // Number of hardware loop register sets (typically 2 for nested loops)
    parameter N_REGS     = 2,
    
    // Bit width for loop register set selection (log2 of N_REGS)
    parameter N_REG_BITS = $clog2(N_REGS)
) (
    input logic clk,     // Clock
    input logic rst_n,   // Active-low reset

    // CSR write interface (from EX stage)
    // Write loop start address (word-aligned, [1:0] forced to 0)
    input logic [          31:0] hwlp_start_data_i,
    
    // Write loop end address (word-aligned, [1:0] forced to 0)
    input logic [          31:0] hwlp_end_data_i,
    
    // Write loop iteration counter
    input logic [          31:0] hwlp_cnt_data_i,
    
    // Write enables: [2]=counter, [1]=end address, [0]=start address
    input logic [           2:0] hwlp_we_i,
    
    // Loop register set selector (0 to N_REGS-1)
    input logic [N_REG_BITS-1:0] hwlp_regid_i,

    // Instruction valid signal (from controller)
    // Gates counter decrement to prevent spurious decrements on stalls
    input logic valid_i,

    // Counter decrement requests (from hwloop controller)
    // One bit per loop: high = decrement this loop's counter
    // Only one bit should be high at a time (asserted)
    input logic [N_REGS-1:0] hwlp_dec_cnt_i,

    // Loop parameter outputs (to hwloop controller)
    // Start addresses for all loops
    output logic [N_REGS-1:0][31:0] hwlp_start_addr_o,
    
    // End addresses for all loops
    output logic [N_REGS-1:0][31:0] hwlp_end_addr_o,
    
    // Iteration counters for all loops
    output logic [N_REGS-1:0][31:0] hwlp_counter_o
);


  ///////////////////////////////////////////////////////////////////////////////
  // Internal Registers
  ///////////////////////////////////////////////////////////////////////////////
  // Storage for all loop parameters
  logic [N_REGS-1:0][31:0] hwlp_start_q;     // Loop start addresses
  logic [N_REGS-1:0][31:0] hwlp_end_q;       // Loop end addresses
  logic [N_REGS-1:0][31:0] hwlp_counter_q;   // Loop iteration counters (current value)
  logic [N_REGS-1:0][31:0] hwlp_counter_n;   // Loop counters next value (decremented)

  int unsigned i;  // Loop variable for generate statements


  // Direct output assignments
  assign hwlp_start_addr_o = hwlp_start_q;
  assign hwlp_end_addr_o   = hwlp_end_q;
  assign hwlp_counter_o    = hwlp_counter_q;


  ///////////////////////////////////////////////////////////////////////////////
  // HWLOOP Start Address Registers
  ///////////////////////////////////////////////////////////////////////////////
  // Store loop start address (beginning of loop body)
  // Address is word-aligned (bits [1:0] forced to 0)
  // Written via CSR instruction with hwlp_we_i[0] asserted
  
  always_ff @(posedge clk, negedge rst_n) begin : HWLOOP_REGS_START
    if (rst_n == 1'b0) begin
      hwlp_start_q <= '{default: 32'b0};  // Reset all start addresses to 0
    end else if (hwlp_we_i[0] == 1'b1) begin
      // Write new start address for selected loop
      // Force word alignment by clearing bits [1:0]
      hwlp_start_q[hwlp_regid_i] <= {hwlp_start_data_i[31:2], 2'b0};
    end
    // else: Hold current value
  end


  ///////////////////////////////////////////////////////////////////////////////
  // HWLOOP End Address Registers
  ///////////////////////////////////////////////////////////////////////////////
  // Store loop end address (address of last instruction in loop body)
  // Address is word-aligned (bits [1:0] forced to 0)
  // Written via CSR instruction with hwlp_we_i[1] asserted
  // When PC matches this address, loop decision is made
  
  always_ff @(posedge clk, negedge rst_n) begin : HWLOOP_REGS_END
    if (rst_n == 1'b0) begin
      hwlp_end_q <= '{default: 32'b0};  // Reset all end addresses to 0
    end else if (hwlp_we_i[1] == 1'b1) begin
      // Write new end address for selected loop
      // Force word alignment by clearing bits [1:0]
      hwlp_end_q[hwlp_regid_i] <= {hwlp_end_data_i[31:2], 2'b0};
    end
    // else: Hold current value
  end


  ///////////////////////////////////////////////////////////////////////////////
  // HWLOOP Counter Decrement Logic (Combinational)
  ///////////////////////////////////////////////////////////////////////////////
  // Pre-compute decremented counter values for all loops
  // Actual decrement happens in sequential block based on hwlp_dec_cnt_i
  
  genvar k;
  for (k = 0; k < N_REGS; k++) begin
    // Next counter value = current - 1
    // Simple decrement, no saturation (counter should not reach 0xFFFFFFFF)
    assign hwlp_counter_n[k] = hwlp_counter_q[k] - 1;
  end

  ///////////////////////////////////////////////////////////////////////////////
  // HWLOOP Counter Registers with Priority Update Logic
  ///////////////////////////////////////////////////////////////////////////////
  // Counter decrements automatically when loop iterates
  // Write has priority over decrement (CSR update takes precedence)
  // valid_i gates decrements to prevent spurious updates during stalls
  
  always_ff @(posedge clk, negedge rst_n) begin : HWLOOP_REGS_COUNTER
    if (rst_n == 1'b0) begin
      hwlp_counter_q <= '{default: 32'b0};  // Reset all counters to 0
    end else begin
      for (i = 0; i < N_REGS; i++) begin
        //---------------------------------------------------------------------
        // Priority 1: CSR Write (Initialize or update counter)
        //---------------------------------------------------------------------
        // When software writes counter via CSR, load new value
        // This has priority over automatic decrement
        if ((hwlp_we_i[2] == 1'b1) && (i == hwlp_regid_i)) begin
          hwlp_counter_q[i] <= hwlp_cnt_data_i;
        end 
        
        //---------------------------------------------------------------------
        // Priority 2: Automatic Decrement (Loop iteration)
        //---------------------------------------------------------------------
        // When controller signals loop taken (hwlp_dec_cnt_i[i] high)
        // and instruction is valid (not stalled), decrement counter
        else begin
          if (hwlp_dec_cnt_i[i] && valid_i) 
            hwlp_counter_q[i] <= hwlp_counter_n[i];
          // else: Hold current value (no update)
        end
      end
    end
  end

  ///////////////////////////////////////////////////////////////////////////////
  // Assertions
  ///////////////////////////////////////////////////////////////////////////////
  // Verify correct usage of hardware loop registers
  
`ifdef CV32E40P_ASSERT_ON
  //-----------------------------------------------------------------------------
  // A1: Only one loop can iterate per cycle
  //-----------------------------------------------------------------------------
  // Multiple loops can be active (nested), but only one can be at its end
  // address in any given cycle. This checks that controller properly
  // prioritizes inner loops.
  // Violation would indicate controller logic error or incorrect nesting
  assert property (@(posedge clk) (valid_i) |-> ($countones(hwlp_dec_cnt_i) <= 1))
  else $error("Multiple hardware loop counters decremented in same cycle!");
`endif

  ///////////////////////////////////////////////////////////////////////////////
  // Implementation Notes
  ///////////////////////////////////////////////////////////////////////////////
  // ALTERNATIVE IMPLEMENTATION: Saturating Counter
  // Add saturation logic to prevent counter underflow:
  //   if (hwlp_counter_q[i] > 0)
  //     hwlp_counter_q[i] <= hwlp_counter_n[i];
  //   else
  //     hwlp_counter_q[i] <= 32'h0;  // Saturate at zero
  // Trade-off: Extra logic vs robustness against software errors
  //
  // ALTERNATIVE IMPLEMENTATION: Counter Width Optimization
  // Most loops have small iteration counts (<256 or <65536)
  // Could use narrower counters with overflow handling:
  //   - 16-bit counter: Saves area, handles 99% of loops
  //   - Overflow flag: Detect when loop count exceeds 16 bits
  //   - Fallback: Use software loop for large counts
  // Trade-off: Area savings vs functionality limitation
  //
  // PERFORMANCE OPTIMIZATION: Counter Prediction
  // For better timing, pre-compute "counter_zero" flag:
  //   assign counter_zero[i] = (hwlp_counter_q[i] == 32'd1);
  // Controller uses this flag instead of comparing counter in critical path
  // Reduces loop decision latency by 1 gate level
  //
  // FPGA IMPLEMENTATION:
  // Register file maps efficiently to distributed RAM or registers
  //   - Xilinx: Can use SRL32 for start/end (constant once set)
  //   - Intel: Use MLABs if N_REGS > 4
  //   - Typical usage: ~200 FFs for N_REGS=2 (6 registers × 32 bits)

endmodule
