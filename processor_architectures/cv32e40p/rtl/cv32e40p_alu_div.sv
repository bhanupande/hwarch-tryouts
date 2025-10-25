// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

///////////////////////////////////////////////////////////////////////////////
// File       : Simple Serial Divider
// Ver        : 1.0
// Date       : 15.03.2016
///////////////////////////////////////////////////////////////////////////////
//
// Description: Serial (iterative) divider for signed and unsigned integers
//
// This module implements a non-restoring division algorithm that computes
// both quotient and remainder for 32-bit signed/unsigned integer division.
// The algorithm executes over multiple clock cycles (serial operation).
//
// Algorithm: Non-Restoring Division
// ----------------------------------
// Non-restoring division is an iterative algorithm that processes one bit
// of the quotient per clock cycle. Unlike restoring division, it doesn't
// restore the partial remainder when the subtraction produces a negative
// result. Instead, it alternates between addition and subtraction based on
// the sign of the partial remainder.
//
// Key characteristics:
// - One bit per cycle throughput (32+ cycles for 32-bit division)
// - Minimal area cost (single adder/subtractor shared across iterations)
// - Handles both signed and unsigned operands
// - Produces both quotient and remainder
// - Special handling for division by zero
//
// Operation Codes (OpCode_SI):
//   00: Unsigned division (udiv)    - quotient only
//   01: Signed division (div)       - quotient only
//   10: Unsigned remainder (urem)   - remainder only
//   11: Signed remainder (rem)      - remainder only
//
// Performance Characteristics:
// - Latency: ~32-35 cycles (depends on operand magnitude)
// - Throughput: 1 operation per ~32 cycles (not pipelined)
// - Area: ~2x adder + shift registers + control FSM
//
// Alternative Implementation Suggestions:
// ----------------------------------------
// 1. Radix-4 Division: Process 2 bits per cycle (halves latency, ~2x area)
// 2. Radix-16 Division: Process 4 bits per cycle (4x faster, 4x area)
// 3. Goldschmidt Algorithm: Faster convergence for certain operand ranges
// 4. SRT Division: Better average-case performance with redundant arithmetic
// 5. Pipelined Divider: Overlap multiple divisions (much higher area cost)
// 6. Look-up Table + Newton-Raphson: Seed from LUT, refine with iteration
//
// For high-performance CPUs, radix-4 or radix-16 is recommended.
// For ultra-low-area designs, this radix-2 implementation is optimal.
///////////////////////////////////////////////////////////////////////////////
//
// Authors    : Michael Schaffner (schaffner@iis.ee.ethz.ch)
//              Andreas Traber    (atraber@iis.ee.ethz.ch)
//
///////////////////////////////////////////////////////////////////////////////

module cv32e40p_alu_div #(
    parameter C_WIDTH     = 32,      // Data width (typically 32 bits)
    parameter C_LOG_WIDTH = 6        // Log2(C_WIDTH+1) for counter width
) (
    // Clock and reset
    input  logic                   Clk_CI,      // Clock input (positive edge triggered)
    input  logic                   Rst_RBI,     // Active-low asynchronous reset
    
    // Operand inputs
    input  logic [    C_WIDTH-1:0] OpA_DI,      // Dividend (numerator)
    input  logic [    C_WIDTH-1:0] OpB_DI,      // Divisor (denominator)
    input  logic [C_LOG_WIDTH-1:0] OpBShift_DI, // Initial shift amount for OpB
                                                 // Optimization: reduces cycles for small divisors
    input  logic                   OpBIsZero_SI, // OpB is zero flag (division by zero handling)
    
    // Operation control
    input  logic                   OpBSign_SI,  // Sign bit of OpB (gate to 0 for unsigned ops)
    input  logic [            1:0] OpCode_SI,   // Operation selection:
                                                 // 00: udiv (unsigned division)
                                                 // 01: div (signed division) 
                                                 // 10: urem (unsigned remainder)
                                                 // 11: rem (signed remainder)
    
    // Handshake interface
    input  logic                   InVld_SI,    // Input valid - start new division
    input  logic                   OutRdy_SI,   // Downstream ready to accept result
    output logic                   OutVld_SO,   // Output valid - result is ready
    
    // Result output
    output logic [    C_WIDTH-1:0] Res_DO       // Division result (quotient or remainder)
);

  ///////////////////////////////////////////////////////////////////////////////
  // Internal Signal Declarations
  ///////////////////////////////////////////////////////////////////////////////

  // Main datapath registers (double-buffered: _DP = present, _DN = next)
  logic [C_WIDTH-1:0] ResReg_DP, ResReg_DN;     // Result register (accumulates quotient bits)
  logic [C_WIDTH-1:0] ResReg_DP_rev;            // Bit-reversed result (quotient built MSB-first)
  logic [C_WIDTH-1:0] AReg_DP, AReg_DN;         // A register (partial remainder)
  logic [C_WIDTH-1:0] BReg_DP, BReg_DN;         // B register (shifted divisor)

  // Control flags for sign handling
  logic RemSel_SN, RemSel_SP;       // Remainder select (1=output remainder, 0=output quotient)
  logic CompInv_SN, CompInv_SP;     // Comparison invert flag (for signed operation)
  logic ResInv_SN, ResInv_SP;       // Result invert flag (negate output if needed)

  // Datapath multiplexers and adder
  logic [C_WIDTH-1:0] AddMux_D;     // Adder input multiplexer output
  logic [C_WIDTH-1:0] AddOut_D;     // Adder output
  logic [C_WIDTH-1:0] AddTmp_D;     // Adder accumulator input
  logic [C_WIDTH-1:0] BMux_D;       // B register input multiplexer
  logic [C_WIDTH-1:0] OutMux_D;     // Output multiplexer (selects quotient or remainder)

  // Iteration counter
  logic [C_LOG_WIDTH-1:0] Cnt_DP, Cnt_DN;  // Counts down from OpBShift_DI to 0
  logic CntZero_S;                          // Counter reached zero (division complete)

  // Control signals
  logic ARegEn_S, BRegEn_S, ResRegEn_S;  // Register enable signals
  logic ABComp_S;                         // A >= B comparison result
  logic PmSel_S;                          // Plus/minus select (add vs subtract)
  logic LoadEn_S;                         // Load enable (initialize for new operation)

  // FSM state definition
  enum logic [1:0] {
    IDLE,    // Waiting for new division request
    DIVIDE,  // Performing iterative division
    FINISH   // Division complete, waiting for result to be consumed
  }
      State_SN, State_SP;


  ///////////////////////////////////////////////////////////////////////////////
  // Datapath Implementation
  ///////////////////////////////////////////////////////////////////////////////

  // Plus/Minus selector for non-restoring algorithm
  // Determines whether to add or subtract in current iteration
  // For signed division, check if signs differ (XOR of sign bits)
  // If signs differ and operation is signed (OpCode_SI[0]), invert operation
  assign PmSel_S  = LoadEn_S & ~(OpCode_SI[0] & (OpA_DI[$high(OpA_DI)] ^ OpBSign_SI));

  // Adder input multiplexer
  // During load: Use OpA_DI (dividend) as initial value
  // During iteration: Use BReg_DP (shifted divisor) for add/subtract
  assign AddMux_D = (LoadEn_S) ? OpA_DI : BReg_DP;

  // B register input multiplexer with right shift
  // During load: Initialize with OpB_DI (divisor)
  // During iteration: Logical right shift by 1 bit
  // Note: Logical shift even for negative operands (uses absolute value internally)
  // MSB gets CompInv_SP to maintain sign information during shift
  assign BMux_D   = (LoadEn_S) ? OpB_DI : {CompInv_SP, (BReg_DP[$high(BReg_DP):1])};

  // Bit reversal logic for quotient result
  // Non-restoring division builds quotient MSB-first in ResReg_DP
  // Need to reverse bits to get correct LSB-first representation
  // Alternative: Could build LSB-first by left-shifting, avoiding reversal
  genvar index;
  generate
    for (index = 0; index < C_WIDTH; index++) begin : gen_bit_swapping
      assign ResReg_DP_rev[index] = ResReg_DP[C_WIDTH-1-index];
    end
  endgenerate

  // Output multiplexer - selects between remainder and quotient
  // RemSel_SP == 1: Output remainder (AReg_DP contains final remainder)
  // RemSel_SP == 0: Output quotient (ResReg_DP_rev contains quotient)
  assign OutMux_D = (RemSel_SP) ? AReg_DP : ResReg_DP_rev;

  // Final output with sign adjustment
  // If ResInv_SP is set, negate the result for proper signed arithmetic
  // Uses $signed cast for correct two's complement negation
  assign Res_DO = (ResInv_SP) ? -$signed(OutMux_D) : OutMux_D;

  // Main comparator for non-restoring division decision
  // Determines quotient bit: 1 if AReg >= BReg (considering sign inversion)
  // Three conditions OR'd together:
  // 1. AReg_DP == BReg_DP: Exactly equal
  // 2. (AReg_DP > BReg_DP) ^ CompInv_SP: Greater-than with sign consideration
  // 3. (|AReg_DP) | OpBIsZero_SI: Non-zero A or division by zero
  // Division by zero handling: Forces comparison true to produce defined result
  assign ABComp_S    = ((AReg_DP == BReg_DP) | ((AReg_DP > BReg_DP) ^ CompInv_SP)) & ((|AReg_DP) | OpBIsZero_SI);

  // Main adder/subtractor
  // Implements the add/subtract operation for non-restoring division
  // AddTmp_D: Previous partial remainder (or 0 during load)
  // AddMux_D: Value to add or subtract (dividend during load, divisor during iteration)
  // PmSel_S controls operation: 1=add, 0=subtract
  assign AddTmp_D = (LoadEn_S) ? 0 : AReg_DP;
  assign AddOut_D = (PmSel_S) ? AddTmp_D + AddMux_D : AddTmp_D - $signed(AddMux_D);

  ///////////////////////////////////////////////////////////////////////////////
  // Iteration Counter Logic
  ///////////////////////////////////////////////////////////////////////////////
  // Tracks number of remaining division iterations
  // Starts at OpBShift_DI (optimization: skips leading zeros in divisor)
  // Decrements each cycle until reaching zero

  // Counter next-state logic
  // LoadEn_S: Initialize counter with shift amount for new operation
  // ~CntZero_S: Decrement counter while not zero (active iteration)
  // CntZero_S: Hold at zero when division complete
  assign Cnt_DN = (LoadEn_S) ? OpBShift_DI : (~CntZero_S) ? Cnt_DP - 1 : Cnt_DP;

  // Zero detection - division complete indicator
  // NOR reduction: true when all counter bits are zero
  assign CntZero_S = ~(|Cnt_DP);

  ///////////////////////////////////////////////////////////////////////////////
  // Finite State Machine (FSM) - Division Control
  ///////////////////////////////////////////////////////////////////////////////
  // Three-state FSM manages division operation lifecycle:
  // IDLE -> DIVIDE -> FINISH -> IDLE
  //
  // Critical Timing Considerations:
  // - State transitions are registered (sequential logic)
  // - Control signals generated combinationally from state
  // - Register enables must settle before clock edge
  // - ABComp_S is on critical path (32-bit comparison + mux)

  always_comb begin : p_fsm
    // Default signal values (override in state-specific logic)
    State_SN   = State_SP;      // Hold current state
    OutVld_SO  = 1'b0;          // No valid output by default
    LoadEn_S   = 1'b0;          // Don't load new operands
    ARegEn_S   = 1'b0;          // Don't update A register
    BRegEn_S   = 1'b0;          // Don't update B register
    ResRegEn_S = 1'b0;          // Don't update result register

    case (State_SP)
      /////////////////////////////////
      // IDLE State: Ready to accept new division request
      // Divider is idle and immediately ready for new operation
      /////////////////////////////////
      IDLE: begin
        OutVld_SO = 1'b1;       // Signal ready/valid in idle state

        if (InVld_SI) begin
          // New division request received
          OutVld_SO = 1'b0;     // No longer valid (starting new operation)
          ARegEn_S  = 1'b1;     // Load dividend into A register
          BRegEn_S  = 1'b1;     // Load divisor into B register
          LoadEn_S  = 1'b1;     // Assert load enable for initialization
          State_SN  = DIVIDE;   // Transition to division state
        end
      end
      
      /////////////////////////////////
      // DIVIDE State: Iterative division in progress
      // Performs one division iteration per clock cycle
      // Updates partial remainder and quotient bit each cycle
      /////////////////////////////////
      DIVIDE: begin
        // Update registers each cycle based on comparison result
        // ARegEn_S controlled by ABComp_S: update A only if subtraction valid
        // This implements the non-restoring division algorithm's conditional update
        ARegEn_S   = ABComp_S;    // Update partial remainder if A >= B
        BRegEn_S   = 1'b1;        // Always shift B right each cycle
        ResRegEn_S = 1'b1;        // Always shift in new quotient bit

        // Check if all iterations complete
        // Counter reaches zero after 32nd iteration (or fewer if OpBShift_DI < 32)
        if (CntZero_S) begin
          State_SN = FINISH;      // Move to output state
        end
      end
      
      /////////////////////////////////
      // FINISH State: Division complete, presenting result
      // Result is valid and waiting for downstream to accept
      // Implements output handshake protocol
      /////////////////////////////////
      FINISH: begin
        OutVld_SO = 1'b1;         // Assert output valid

        if (OutRdy_SI) begin
          // Downstream consumed result, ready for next operation
          State_SN = IDLE;        // Return to idle state
        end
      end
      
      /////////////////////////////////
      default:  /* default case for synthesis (prevents latches) */;
      /////////////////////////////////
    endcase
  end


  ///////////////////////////////////////////////////////////////////////////////
  // Register Update Logic (Combinational Next-State)
  ///////////////////////////////////////////////////////////////////////////////
  // Determines next values for all datapath registers based on current
  // operation state and control signals

  // Control flags for result processing
  // RemSel: Select remainder (1) or quotient (0) for output
  // Set during load based on operation code bit [1]
  assign RemSel_SN = (LoadEn_S) ? OpCode_SI[1] : RemSel_SP;
  
  // CompInv: Comparison inversion flag for signed arithmetic
  // Set to OpB sign bit during load, held during iteration
  assign CompInv_SN = (LoadEn_S) ? OpBSign_SI : CompInv_SP;
  
  // ResInv: Result inversion flag (negate output)
  // Complex logic handles sign of result for signed division:
  // - For division by zero: Don't invert (unless remainder requested)
  // - For signed operations: Invert if operand signs differ
  // OpCode_SI[0]: 1 for signed operations, 0 for unsigned
  // OpCode_SI[1]: 1 for remainder, 0 for quotient
  assign ResInv_SN = (LoadEn_S) ? (~OpBIsZero_SI | OpCode_SI[1]) & OpCode_SI[0] & (OpA_DI[$high(
      OpA_DI
  )] ^ OpBSign_SI) : ResInv_SP;

  // A Register (Partial Remainder) update
  // Updated only when ABComp_S indicates valid subtraction/addition
  // Holds partial remainder through division iterations
  assign AReg_DN = (ARegEn_S) ? AddOut_D : AReg_DP;
  
  // B Register (Shifted Divisor) update  
  // Shifts right by 1 bit each iteration (dividing divisor by 2)
  // Allows comparison with progressively smaller divisor values
  assign BReg_DN = (BRegEn_S) ? BMux_D : BReg_DP;
  
  // Result Register (Quotient Accumulator) update
  // During load: Clear to zero
  // During iteration: Shift left and insert new quotient bit (ABComp_S)
  // Builds quotient MSB-first (will be reversed later)
  assign ResReg_DN = (LoadEn_S) ? '0 : (ResRegEn_S) ? {
    ABComp_S, ResReg_DP[$high(ResReg_DP):1]
  } : ResReg_DP;

  ///////////////////////////////////////////////////////////////////////////////
  // Sequential Logic - Register File
  ///////////////////////////////////////////////////////////////////////////////
  // All datapath and control registers update on positive clock edge
  // Asynchronous active-low reset initializes to safe/known state
  //
  // Critical Timing Path:
  // The combinational logic feeding these registers includes:
  // - 32-bit comparison (ABComp_S)
  // - 32-bit add/subtract (AddOut_D)
  // - Multiple levels of multiplexers
  // This is typically the critical path in the divider

  always_ff @(posedge Clk_CI or negedge Rst_RBI) begin : p_regs
    if (~Rst_RBI) begin
      // Reset state: Initialize to IDLE with cleared registers
      State_SP   <= IDLE;
      AReg_DP    <= '0;       // Clear partial remainder
      BReg_DP    <= '0;       // Clear shifted divisor
      ResReg_DP  <= '0;       // Clear result accumulator
      Cnt_DP     <= '0;       // Clear iteration counter
      RemSel_SP  <= 1'b0;     // Default to quotient output
      CompInv_SP <= 1'b0;     // No comparison inversion
      ResInv_SP  <= 1'b0;     // No result inversion
    end else begin
      // Normal operation: Update all registers with next values
      State_SP   <= State_SN;
      AReg_DP    <= AReg_DN;
      BReg_DP    <= BReg_DN;
      ResReg_DP  <= ResReg_DN;
      Cnt_DP     <= Cnt_DN;
      RemSel_SP  <= RemSel_SN;
      CompInv_SP <= CompInv_SN;
      ResInv_SP  <= ResInv_SN;
    end
  end

  ///////////////////////////////////////////////////////////////////////////////
  // Formal Verification Assertions
  ///////////////////////////////////////////////////////////////////////////////
  // Design-time checks to verify parameter correctness
  // These assertions run during elaboration (before simulation)

`ifdef CV32E40P_ASSERT_ON
  initial begin : p_assertions
    // Verify counter width is correctly sized for data width
    // C_LOG_WIDTH must be ceil(log2(C_WIDTH+1)) to count from C_WIDTH down to 0
    // For C_WIDTH=32, need C_LOG_WIDTH=6 (can represent 0-32, which is 33 values)
    assert (C_LOG_WIDTH == $clog2(C_WIDTH + 1))
    else $error("C_LOG_WIDTH must be $clog2(C_WIDTH+1)");
    
    // Additional assertions that could enhance verification:
    //
    // 1. Division by zero produces architecturally-defined result
    // 2. Signed division handles INT_MIN / -1 correctly (overflow case)
    // 3. Remainder sign matches dividend sign (per RISC-V spec)
    // 4. No state machine deadlocks (eventually returns to IDLE)
    // 5. Output valid deasserts when new operation starts
  end
`endif

endmodule  // cv32e40p_alu_div
