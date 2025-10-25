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
// Engineer:       Pasquale Davide Schiavone - pschiavo@iis.ee.ethz.ch        //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@greenwaves-technologies.com            //
//                                                                            //
// Design Name:    Instruction Aligner                                        //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Instruction Aligner Module                                 //
//                                                                            //
// The aligner is responsible for aligning instructions fetched from memory  //
// to present properly formatted 32-bit instructions to the decode stage.    //
// RISC-V supports both 16-bit compressed (RVC) and 32-bit standard          //
// instructions, which can be misaligned across 32-bit word boundaries.      //
//                                                                            //
// Key Responsibilities:                                                      //
// 1. Handle 32-bit aligned instructions (simple passthrough)                //
// 2. Handle 16-bit compressed instructions at any alignment                 //
// 3. Handle 32-bit instructions that span two consecutive memory words      //
// 4. Manage state transitions when branches/jumps change alignment          //
// 5. Support hardware loop address updates                                  //
//                                                                            //
// State Machine Description:                                                //
// - ALIGNED32: Current PC is 4-byte aligned, last instr was 32-bit         //
// - MISALIGNED32: PC is 2-byte aligned, need upper half from next word     //
// - MISALIGNED16: Have cached upper half, waiting to use it                //
// - BRANCH_MISALIGNED: Branched to misaligned address, need to realign     //
// - WAIT_VALID_BRANCH: Waiting for valid data after branch (if used)       //
//                                                                            //
// Critical Timing Paths:                                                     //
// - Alignment mux selection (fetch_rdata_i to instr_aligned_o)             //
// - State machine next-state logic                                          //
// - PC increment logic (pc_plus2/pc_plus4)                                  //
//                                                                            //
// Alternative Implementation Suggestions:                                    //
// 1. FIFO-based approach: Use a small FIFO to buffer fetched data and      //
//    extract instructions on-demand. This simplifies state machine but     //
//    increases area and may impact timing.                                  //
// 2. Dual-port approach: Fetch 64 bits per cycle to always have complete   //
//    instruction available, eliminating misalignment stalls.                //
// 3. Speculative alignment: Pre-compute both aligned and misaligned        //
//    versions in parallel, select based on compressed bit at decode.        //
////////////////////////////////////////////////////////////////////////////////

module cv32e40p_aligner (
    input logic clk,     // Clock signal - positive edge triggered
    input logic rst_n,   // Active-low asynchronous reset

    // Fetch stage interface
    input  logic fetch_valid_i,      // Valid instruction data from fetch stage
    output logic aligner_ready_o,    // Aligner ready to accept new fetch data
                                     // Prevents overwriting fetched instruction when we need to buffer it

    input logic if_valid_i,          // Instruction fetch stage is valid (downstream ready)

    // Instruction data interface
    input  logic [31:0] fetch_rdata_i,     // Raw 32-bit word from instruction memory
    output logic [31:0] instr_aligned_o,   // Aligned instruction output to decode stage
    output logic        instr_valid_o,     // Aligned instruction is valid

    // Branch/Jump control interface
    input logic [31:0] branch_addr_i,      // Target address for branch/jump
    input logic        branch_i,           // Branch/jump taken signal (from EX stage)

    // Hardware loop interface
    input logic [31:0] hwlp_addr_i,        // Hardware loop jump target address
    input logic        hwlp_update_pc_i,   // Hardware loop PC update request

    // Program counter output
    output logic [31:0] pc_o               // Current program counter value
);

  // State machine enumeration
  // Tracks current alignment state and determines how to process incoming fetch data
  enum logic [2:0] {
    ALIGNED32,          // PC is 4-byte aligned, last instruction was 32-bit
                        // Next fetch will be naturally aligned
    MISALIGNED32,       // PC is at offset +2 within word, expecting 32-bit instruction
                        // Lower 16 bits come from previous fetch, upper 16 from current
    MISALIGNED16,       // PC is at offset +2, last was 16-bit compressed instruction
                        // Upper 16 bits of previous word contain next instruction start
    BRANCH_MISALIGNED,  // Just branched to misaligned address (addr[1] = 1)
                        // Need to extract instruction from upper half of fetched word
    WAIT_VALID_BRANCH   // Reserved state for branch delay handling (if needed)
  }
      state, next_state;

  // Internal state registers
  logic [15:0] r_instr_h;          // Buffered upper 16 bits from previous fetch
                                    // Used when 32-bit instruction spans word boundary
  logic [31:0] hwlp_addr_q;         // Registered hardware loop target address
  logic [31:0] pc_q, pc_n;          // Current and next PC values
  logic update_state;               // Control signal to update FSM state and registers
  logic [31:0] pc_plus4, pc_plus2;  // Pre-computed PC increments for timing optimization
  logic aligner_ready_q;            // Registered version of aligner_ready_o
  logic hwlp_update_pc_q;           // Registered hardware loop update request

  // Continuous assignments for PC and increments
  assign pc_o     = pc_q;           // Drive output PC

  // Pre-compute PC increments to reduce critical path delay
  // These are always computed; mux selection determines which is used
  assign pc_plus2 = pc_q + 2;       // For 16-bit compressed instructions
  assign pc_plus4 = pc_q + 4;       // For 32-bit standard instructions

  // Sequential state machine and register update
  // Updates on positive clock edge, asynchronous active-low reset
  always_ff @(posedge clk or negedge rst_n) begin : proc_SEQ_FSM
    if (~rst_n) begin
      // Reset to aligned state
      state            <= ALIGNED32;    // Assume reset vector is 4-byte aligned
      r_instr_h        <= '0;           // Clear instruction buffer
      hwlp_addr_q      <= '0;           // Clear hardware loop address
      pc_q             <= '0;           // Reset PC to zero (boot address set externally)
      aligner_ready_q  <= 1'b0;         // Not ready initially
      hwlp_update_pc_q <= 1'b0;         // No pending hardware loop update
    end else begin
      if (update_state) begin
        // Normal state update path - advance FSM and update registers
        pc_q             <= pc_n;                    // Update PC
        state            <= next_state;              // Advance state machine
        r_instr_h        <= fetch_rdata_i[31:16];   // Buffer upper half for potential use
        aligner_ready_q  <= aligner_ready_o;         // Register ready signal
        hwlp_update_pc_q <= 1'b0;                    // Clear hardware loop flag after use
      end else begin
        // State update is blocked (stall condition)
        // But still need to capture hardware loop requests
        if (hwlp_update_pc_i) begin
          hwlp_addr_q      <= hwlp_addr_i;  // Save jump target address during stall
                                             // Ensures PC stays synchronized when stall ends
          hwlp_update_pc_q <= 1'b1;         // Flag that update is pending
        end

      end
    end
  end

  // Combinational next-state logic and output generation
  // This block determines:
  // 1. Next state based on current state and instruction size (bits [1:0])
  // 2. Aligned instruction output (may combine parts from multiple fetches)
  // 3. PC update value
  // 4. Handshaking signals (valid, ready, update_state)
  always_comb begin

    // Default outputs - these are overridden in state-specific logic below
    pc_n            = pc_q;           // Hold PC by default (no increment)
    instr_valid_o   = fetch_valid_i;  // Valid output tracks fetch valid
    instr_aligned_o = fetch_rdata_i;  // Pass through fetch data by default
    aligner_ready_o = 1'b1;           // Ready to accept new data by default
    update_state    = 1'b0;           // Don't update state by default
    next_state      = state;          // Hold current state by default


    case (state)
      ALIGNED32: begin
        // Current state: PC is 4-byte aligned
        // Fetch data contains complete instruction starting at bit 0
        // Check bits[1:0] to determine if instruction is 16-bit (!=11) or 32-bit (==11)
        
        if (fetch_rdata_i[1:0] == 2'b11) begin
          // Current instruction is 32-bit (standard RISC-V encoding)
          // Instruction: fetch_rdata_i[31:0]
          // Next PC: +4 (stay aligned)
          next_state      = ALIGNED32;
          pc_n            = pc_plus4;
          instr_aligned_o = fetch_rdata_i;
          // Update state only when both fetch is valid and downstream can accept
          // Gate with fetch_valid_i because we need valid data to determine next state
          update_state    = fetch_valid_i & if_valid_i;
          
          // Handle hardware loop PC updates
          // Hardware loops can modify PC even during normal operation
          if (hwlp_update_pc_i || hwlp_update_pc_q)
            pc_n = hwlp_update_pc_i ? hwlp_addr_i : hwlp_addr_q;
        end else begin
          // Current instruction is 16-bit compressed (RVC encoding)
          // Instruction: fetch_rdata_i[15:0]
          // Upper 16 bits (fetch_rdata_i[31:16]) are the start of next instruction
          // Next PC: +2 (becomes misaligned)
          next_state      = MISALIGNED32;
          pc_n            = pc_plus2;
          instr_aligned_o = fetch_rdata_i;  // Decoder will use only lower 16 bits
          // Gate with fetch_valid_i because next state depends on instruction size
          update_state    = fetch_valid_i & if_valid_i;
        end
      end


      MISALIGNED32: begin
        // Current state: PC is at +2 offset within a word
        // r_instr_h contains the lower 16 bits of current instruction
        // Check r_instr_h[1:0] to determine instruction size
        
        if (r_instr_h[1:0] == 2'b11) begin
          // Current instruction is 32-bit and spans two fetches
          // Lower 16 bits: r_instr_h (from previous fetch)
          // Upper 16 bits: fetch_rdata_i[15:0] (from current fetch)
          // Remaining data: fetch_rdata_i[31:16] (start of next instruction)
          next_state      = MISALIGNED32;
          pc_n            = pc_plus4;
          instr_aligned_o = {fetch_rdata_i[15:0], r_instr_h[15:0]};
          // Gate with fetch_valid_i because we need current fetch to complete instruction
          update_state    = fetch_valid_i & if_valid_i;
        end else begin
          // Current instruction is 16-bit compressed
          // Instruction: r_instr_h[15:0] (from previous fetch)
          // Current fetch contains: {next_instr_start[15:0], current_instr[15:0]}
          // But we already have current_instr in r_instr_h, so we present it
          // and transition to MISALIGNED16 to handle the fetched word next cycle
          instr_aligned_o = {fetch_rdata_i[31:16], r_instr_h[15:0]};  // Assemble for output
          next_state      = MISALIGNED16;
          instr_valid_o   = 1'b1;       // Instruction is valid (we have all bits)
          pc_n            = pc_plus2;
          
          // Critical flow control:
          // We cannot overwrite fetch_rdata_i because it contains the next instruction
          // Tell IF stage to stall if there's new valid data incoming
          // The new fetch goes to the prefetch FIFO instead
          aligner_ready_o = !fetch_valid_i;
          
          // Don't need to gate with fetch_valid_i here because:
          // - Current instruction is complete (from r_instr_h)
          // - Next state determination only depends on r_instr_h, not new fetch
          update_state    = if_valid_i;
        end
      end


      MISALIGNED16: begin
        // Current state: Previous instruction was 16-bit at misaligned address
        // We have buffered the fetch word that contains the next instruction
        // (because we held aligner_ready_o low in previous state)
        
        // Instruction is valid if:
        // - We were not ready last cycle (have buffered data), OR
        // - New valid fetch has arrived
        instr_valid_o = !aligner_ready_q || fetch_valid_i;
        
        if (fetch_rdata_i[1:0] == 2'b11) begin
          // Next instruction is 32-bit
          // It's naturally aligned at bit 0 of the fetched word
          // After this, we return to aligned state
          next_state      = ALIGNED32;
          pc_n            = pc_plus4;
          instr_aligned_o = fetch_rdata_i;
          // Update when instruction is valid (buffered or new) and downstream ready
          // No need to gate with fetch_valid_i because data was held from previous cycle
          update_state    = (!aligner_ready_q | fetch_valid_i) & if_valid_i;
        end else begin
          // Next instruction is 16-bit compressed
          // Lower 16 bits contain current instruction
          // Upper 16 bits contain start of next instruction
          // Transition back to MISALIGNED32 state
          next_state = MISALIGNED32;
          pc_n = pc_plus2;
          instr_aligned_o = fetch_rdata_i;  // Decoder uses lower 16 bits only
          // Update when instruction is valid (buffered or new) and downstream ready
          update_state = (!aligner_ready_q | fetch_valid_i) & if_valid_i;
        end
      end


      BRANCH_MISALIGNED: begin
        // Current state: Just branched to misaligned address (branch_addr_i[1] == 1)
        // Fetched word contains: {useful_instr[15:0], unused_data[15:0]}
        // The instruction starts at bit 16 of the fetched word
        // Check bits [17:16] to determine instruction size
        
        if (fetch_rdata_i[17:16] == 2'b11) begin
          // Instruction at misaligned branch target is 32-bit
          // Lower 16 bits: fetch_rdata_i[31:16] (current fetch upper half)
          // Upper 16 bits: will come from next fetch
          // Transition to MISALIGNED32 to get remaining bits
          next_state      = MISALIGNED32;
          instr_valid_o   = 1'b0;       // Not valid yet - need another fetch
          pc_n            = pc_q;        // Hold PC (don't increment yet)
          instr_aligned_o = fetch_rdata_i;  // Pass through (will be ignored due to !valid)
          // Gate with fetch_valid_i because we need to see instruction bits to determine size
          update_state    = fetch_valid_i & if_valid_i;
        end else begin
          // Instruction at misaligned branch target is 16-bit compressed
          // Instruction bits: fetch_rdata_i[31:16]
          // Since we consumed the entire useful portion of the word, 
          // we can return to ALIGNED32 state for next fetch
          next_state = ALIGNED32;
          pc_n = pc_plus2;
          // Replicate upper 16 bits to both halves
          // (Decoder will ignore upper half for 16-bit instruction)
          instr_aligned_o = {
            fetch_rdata_i[31:16], fetch_rdata_i[31:16]
          };
          // Gate with fetch_valid_i because we need valid data to know instruction size
          update_state = fetch_valid_i & if_valid_i;
        end
      end

    endcase  // state


    // Branch/Jump override logic
    // When branch_i is asserted (from EX stage), immediately update PC and state
    // This overrides the normal sequential instruction flow
    // Branch takes highest priority and forces state update regardless of other conditions
    if (branch_i) begin
      update_state = 1'b1;              // Force state update
      pc_n         = branch_addr_i;     // Load new PC from branch target
      // Determine next state based on branch target alignment:
      // - If branch_addr_i[1] == 1: misaligned, need BRANCH_MISALIGNED state
      // - If branch_addr_i[1] == 0: aligned, can use ALIGNED32 state
      next_state   = branch_addr_i[1] ? BRANCH_MISALIGNED : ALIGNED32;
    end

  end

  /*
  Design Note: Branch Timing and Validation
  
  When a branch is taken in the EX stage, if_valid_i is asserted even during stalls
  because the branch information is captured and stored in the IF stage (prefetcher) 
  when branch_i is asserted. This design decision ensures:
  
  1. Branch resolution is not lost during pipeline stalls
  2. Branch target address is preserved for correct PC update
  3. Clean separation between branch decision (EX) and instruction alignment (IF)
  
  Alternative Implementation Consideration:
  Some designs might buffer the branch target in the aligner itself rather than
  relying on the prefetcher to hold state. This would add one more register but
  could simplify the interface protocol and make the design more robust to
  timing variations between stages.
  
  Theoretical Note:
  Strictly speaking, we don't need to save the instruction after a taken branch
  since the branch invalidates the sequential instruction stream. However, the
  current implementation provides a cleaner hardware structure and more robust
  behavior during corner cases.
*/

  //////////////////////////////////////////////////////////////////////////////
  // Formal Verification Assertions
  //////////////////////////////////////////////////////////////////////////////
  // These assertions help verify correct operation during simulation and
  // formal verification, catching design bugs and protocol violations

`ifdef CV32E40P_ASSERT_ON

  // Hardware Loop PC Update Assertion
  // Verifies that hardware loop updates don't conflict
  // Only one of hwlp_update_pc_i (new request) or hwlp_update_pc_q (buffered request)
  // should be active at any given time, never both simultaneously
  // This prevents race conditions in PC update logic
  property p_hwlp_update_pc;
    @(posedge clk) disable iff (!rst_n) (1'b1) |-> (!(hwlp_update_pc_i && hwlp_update_pc_q));
  endproperty

  a_hwlp_update_pc :
  assert property (p_hwlp_update_pc);

  // Additional assertions that could be added for more comprehensive verification:
  //
  // 1. State transition coverage: Ensure all valid state transitions are reachable
  // 2. PC increment correctness: Verify PC always increments by 2 or 4, never other values
  // 3. Alignment consistency: Check that PC[1] matches expected alignment state
  // 4. No instruction loss: Verify that valid instructions are never dropped
  // 5. Branch target alignment: Ensure branch targets maintain correct alignment state

`endif

endmodule
