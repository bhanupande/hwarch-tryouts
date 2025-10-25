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
// Design Name:    Find First One (Priority Encoder)                          //
// Project Name:   RI5CY / CV32E40P                                           //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Parameterized find-first-one (priority encoder) module     //
//                                                                            //
// This module implements a priority encoder that finds the position of the   //
// least significant '1' bit in the input vector. It uses a tree-based       //
// approach for O(log N) delay instead of linear scan O(N).                  //
//                                                                            //
// Algorithm: Binary Tree Priority Encoder                                    //
// ----------------------------------------                                   //
// The implementation builds a binary tree with NUM_LEVELS levels where       //
// NUM_LEVELS = ceil(log2(LEN)). Each node in the tree:                      //
// 1. Combines two child nodes' selection signals (OR operation)             //
// 2. Propagates the index from the left child if it has a '1', else right   //
//                                                                            //
// Tree Structure Example (LEN=8):                                            //
//                      Root (Level 0)                                        //
//                    /                \                                      //
//              Node0 (L1)         Node1 (L1)                                 //
//             /        \          /        \                                 //
//        N0(L2)     N1(L2)    N2(L2)    N3(L2)                              //
//        /  \       /  \      /  \      /  \                                //
//      i[0] i[1]  i[2] i[3]  i[4] i[5] i[6] i[7]                           //
//                                                                            //
// Delay Characteristics:                                                     //
// - Levels: log2(LEN) = 5 for 32-bit input                                  //
// - Each level: 2-input mux delay                                           //
// - Total: ~5 mux delays for 32-bit (much better than 32-input priority)    //
//                                                                            //
// Usage in CV32E40P:                                                         //
// - CLZ (Count Leading Zeros): Find first '1' in bit-reversed input         //
// - Interrupt priority: Find highest priority pending interrupt             //
// - Bit manipulation: General priority encoding operations                  //
//                                                                            //
// Alternative Implementations:                                               //
// ----------------------------                                               //
// 1. Linear Priority Encoder: Check each bit sequentially                   //
//    Benefit: Minimal area                                                  //
//    Cost: O(N) delay - unacceptable for 32-bit                             //
//                                                                            //
// 2. One-Hot Encoder + OR Tree: Convert to one-hot, then sum indices       //
//    Benefit: Slightly simpler logic                                        //
//    Cost: More levels of logic, higher power                               //
//                                                                            //
// 3. Look-Up Table: Synthesize as ROM/LUT                                   //
//    Benefit: Single-cycle guaranteed                                       //
//    Cost: 2^N entries impractical for N>8                                  //
//                                                                            //
// 4. Logarithmic Scan: Binary search approach                               //
//    Benefit: More regular structure                                        //
//    Cost: Similar delay to tree, more complex control                      //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40p_ff_one #(
    parameter LEN = 32  // Width of input vector (typically 32 for register width)
) (
    input logic [LEN-1:0] in_i,           // Input bit vector to scan

    output logic [$clog2(LEN)-1:0] first_one_o,  // Index of first (LSB) '1' bit
    output logic                   no_ones_o     // Flag: no '1' bits found (all zeros)
);

  // Calculate tree depth based on input width
  localparam NUM_LEVELS = $clog2(LEN);

  // Look-up table: Maps each input bit position to its index
  logic [          LEN-1:0][NUM_LEVELS-1:0] index_lut;
  
  // Tree node signals
  // sel_nodes: Selection signal (OR of children) for each node
  // index_nodes: Index value propagating through tree
  logic [2**NUM_LEVELS-1:0]                 sel_nodes;
  logic [2**NUM_LEVELS-1:0][NUM_LEVELS-1:0] index_nodes;


  //////////////////////////////////////////////////////////////////////////////
  // Generate Tree Structure
  //////////////////////////////////////////////////////////////////////////////
  // Build a complete binary tree for priority encoding
  // Tree is indexed: root at [0], children of node[i] at [2i+1] and [2i+2]

  // Generate index look-up table - each position maps to its own index
  generate
    genvar j;
    for (j = 0; j < LEN; j++) begin : gen_index_lut
      assign index_lut[j] = $unsigned(j);
    end
  endgenerate

  // Build the binary tree level by level, from leaves (inputs) to root
  // Tree construction proceeds bottom-up: leaf level first, then internal nodes
  generate
    genvar k;
    genvar l;
    genvar level;

    // Initialize root node (will be computed from children)
    assign sel_nodes[2**NUM_LEVELS-1] = 1'b0;

    for (level = 0; level < NUM_LEVELS; level++) begin : gen_tree
      //------------------------------------------------------------
      // Non-root levels: Combine children nodes
      //------------------------------------------------------------
      if (level < NUM_LEVELS - 1) begin : gen_non_root_level
        for (l = 0; l < 2 ** level; l++) begin : gen_node
          // Selection: OR of two children (does either child have a '1'?)
          assign sel_nodes[2**level-1+l]   = sel_nodes[2**(level+1)-1+l*2] | sel_nodes[2**(level+1)-1+l*2+1];
          // Index: Propagate left child if it has '1', else propagate right
          // This implements priority: left (lower index) takes precedence
          assign index_nodes[2**level-1+l] = (sel_nodes[2**(level+1)-1+l*2] == 1'b1) ?
                                           index_nodes[2**(level+1)-1+l*2] : index_nodes[2**(level+1)-1+l*2+1];
        end
      end
      
      //------------------------------------------------------------
      // Root level (leaf nodes): Connect directly to input bits
      //------------------------------------------------------------
      if (level == NUM_LEVELS - 1) begin : gen_root_level
        for (k = 0; k < 2 ** level; k++) begin : gen_node
          // Case 1: Two successive input bits are both within vector bounds
          if (k * 2 < LEN - 1) begin : gen_two
            assign sel_nodes[2**level-1+k] = in_i[k*2] | in_i[k*2+1];
            assign index_nodes[2**level-1+k] = (in_i[k*2] == 1'b1) ? index_lut[k*2] : index_lut[k*2+1];
          end
          
          // Case 2: Only first bit is within bounds (odd-length input)
          if (k * 2 == LEN - 1) begin : gen_one
            assign sel_nodes[2**level-1+k]   = in_i[k*2];
            assign index_nodes[2**level-1+k] = index_lut[k*2];
          end
          
          // Case 3: Both indices out of range (padding for non-power-of-2 lengths)
          // Fill with zero so they don't affect parent node's OR operation
          if (k * 2 > LEN - 1) begin : gen_out_of_range
            assign sel_nodes[2**level-1+k]   = 1'b0;
            assign index_nodes[2**level-1+k] = '0;
          end
        end
      end
      //------------------------------------------------------------
    end
  endgenerate

  //////////////////////////////////////////////////////////////////////////////
  // Output Assignments
  //////////////////////////////////////////////////////////////////////////////
  // Root node contains the final result
  
  // Index of first '1' bit (0 to LEN-1)
  // Undefined if no_ones_o is true (all input bits are 0)
  assign first_one_o = index_nodes[0];
  
  // Flag indicating input is all zeros
  // Inverted selection bit: sel_nodes[0] is true if any input bit is '1'
  assign no_ones_o   = ~sel_nodes[0];

endmodule
