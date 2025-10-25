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
// Engineer:       Andreas Traber - atraber@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Population Count (Hamming Weight)                          //
// Project Name:   RI5CY / CV32E40P                                           //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Count the number of '1' bits in a 32-bit word              //
//                                                                            //
// This module implements the population count (popcount) operation, also     //
// known as Hamming weight or sideways sum. It counts how many bits are set  //
// to '1' in the input word.                                                  //
//                                                                            //
// Algorithm: Binary Tree Reduction                                           //
// ---------------------------------                                          //
// Uses a 5-level tree of adders to sum all bits efficiently:                //
//                                                                            //
// Level 1 (16 adders): Pairs of bits      -> 16 x 2-bit sums (0-2)         //
// Level 2 ( 8 adders): Pairs of 2-bit     ->  8 x 3-bit sums (0-4)         //
// Level 3 ( 4 adders): Pairs of 3-bit     ->  4 x 4-bit sums (0-8)         //
// Level 4 ( 2 adders): Pairs of 4-bit     ->  2 x 5-bit sums (0-16)        //
// Level 5 ( 1 adder ): Pair of 5-bit      ->  1 x 6-bit sum  (0-32)        //
//                                                                            //
// Total: 31 small adders arranged in 5 levels                               //
// Delay: ~5 adder delays (much better than 31-input adder tree)             //
//                                                                            //
// Usage in RISC-V:                                                           //
// - CPOP instruction (RV32B Bit Manipulation extension)                      //
// - Used in cryptography, error correction, and data compression            //
//                                                                            //
// Area/Delay Trade-offs:                                                     //
// ----------------------                                                     //
// This implementation optimizes for delay (O(log n)) at cost of area.       //
//                                                                            //
// Alternative Implementations:                                               //
// ----------------------------                                               //
// 1. LUT-based: Use 4x 256-entry LUTs (one per byte)                       //
//    Benefit: Constant single-cycle delay                                   //
//    Cost: 1KB of ROM/LUT resources                                         //
//                                                                            //
// 2. Iterative: Count one bit per cycle                                     //
//    Benefit: Minimal area (1 accumulator + counter)                        //
//    Cost: 32-cycle latency - unacceptable for single-cycle ALU             //
//                                                                            //
// 3. Parallel Prefix: Use carry-save adders                                 //
//    Benefit: Slightly better timing                                        //
//    Cost: More complex, harder to synthesize efficiently                   //
//                                                                            //
// 4. SWAR (SIMD Within A Register): Parallel byte-wise counting            //
//    Benefit: Good for wider inputs (64/128-bit)                            //
//    Cost: More complex control logic                                       //
//                                                                            //
// Critical Timing Path:                                                      //
// ---------------------                                                      //
// Through all 5 levels of adders: Level1 -> Level2 -> ... -> Level5        //
// Each level adds ~1 gate delay. Modern synthesis tools can optimize        //
// the adder tree for the target technology.                                 //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40p_popcnt (
    input  logic [31:0] in_i,      // Input word to count '1' bits
    output logic [ 5:0] result_o   // Count of '1' bits (0 to 32)
);

  ///////////////////////////////////////////////////////////////////////////////
  // Level 1: Pair-wise addition of individual bits
  ///////////////////////////////////////////////////////////////////////////////
  // 16 small adders: Add pairs of bits to get 2-bit counts (0, 1, or 2)
  // Result range: 0-2 (needs 2 bits)
  logic [15:0][1:0] cnt_l1;
  
  ///////////////////////////////////////////////////////////////////////////////
  // Level 2: Pair-wise addition of 2-bit counts  
  ///////////////////////////////////////////////////////////////////////////////
  // 8 adders: Add pairs of 2-bit values to get 3-bit counts
  // Result range: 0-4 (needs 3 bits)
  logic [ 7:0][2:0] cnt_l2;
  
  ///////////////////////////////////////////////////////////////////////////////
  // Level 3: Pair-wise addition of 3-bit counts
  ///////////////////////////////////////////////////////////////////////////////
  // 4 adders: Add pairs of 3-bit values to get 4-bit counts
  // Result range: 0-8 (needs 4 bits)
  logic [ 3:0][3:0] cnt_l3;
  
  ///////////////////////////////////////////////////////////////////////////////
  // Level 4: Pair-wise addition of 4-bit counts
  ///////////////////////////////////////////////////////////////////////////////
  // 2 adders: Add pairs of 4-bit values to get 5-bit counts
  // Result range: 0-16 (needs 5 bits)
  logic [ 1:0][4:0] cnt_l4;

  // Generate Level 1: Bit pairs
  genvar l, m, n, p;
  generate
    for (l = 0; l < 16; l++) begin : gen_cnt_l1
      // Add two adjacent bits, zero-extend to 2 bits
      assign cnt_l1[l] = {1'b0, in_i[2*l]} + {1'b0, in_i[2*l+1]};
    end
  endgenerate

  // Generate Level 2: Combine 2-bit counts
  generate
    for (m = 0; m < 8; m++) begin : gen_cnt_l2
      // Add two 2-bit counts, zero-extend to 3 bits
      assign cnt_l2[m] = {1'b0, cnt_l1[2*m]} + {1'b0, cnt_l1[2*m+1]};
    end
  endgenerate

  // Generate Level 3: Combine 3-bit counts
  generate
    for (n = 0; n < 4; n++) begin : gen_cnt_l3
      // Add two 3-bit counts, zero-extend to 4 bits
      assign cnt_l3[n] = {1'b0, cnt_l2[2*n]} + {1'b0, cnt_l2[2*n+1]};
    end
  endgenerate

  // Generate Level 4: Combine 4-bit counts
  generate
    for (p = 0; p < 2; p++) begin : gen_cnt_l4
      // Add two 4-bit counts, zero-extend to 5 bits
      assign cnt_l4[p] = {1'b0, cnt_l3[2*p]} + {1'b0, cnt_l3[2*p+1]};
    end
  endgenerate

  ///////////////////////////////////////////////////////////////////////////////
  // Level 5 (Final): Combine two 5-bit counts into 6-bit result
  ///////////////////////////////////////////////////////////////////////////////
  // Add the two halves (each counting up to 16 bits) to get final count
  // Result range: 0-32 (needs 6 bits)
  assign result_o = {1'b0, cnt_l4[0]} + {1'b0, cnt_l4[1]};

endmodule
