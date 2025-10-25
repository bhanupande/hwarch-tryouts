// Copyright 2020 Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License").
//
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
//
// You may obtain a copy of the License at:
//
//     https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS
// OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
//
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Arjan Bink - arjan.bink@silabs.com                         //
//                                                                            //
// Design Name:    Prefetcher Controller                                      //
// Project Name:   CV32E40P                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Prefetch Controller which receives control flow            //
//                 information (req_i, branch_*) from the Fetch stage         //
//                 and based on that performs transactions requests to the    //
//                 bus interface adapter instructions. Prefetching based on   //
//                 incrementing addressed is performed when no new control    //
//                 flow change is requested. New transaction requests are     //
//                 only performed if it can be guaranteed that the fetch FIFO //
//                 will not overflow (resulting in a maximum of DEPTH         //
//                 outstanding transactions.                                  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Module: cv32e40p_prefetch_controller
///////////////////////////////////////////////////////////////////////////////
//
// FUNCTION:
//   FSM controlling instruction prefetch operations.
//   Manages transaction requests, address generation, and response handling.
//
// ARCHITECTURE:
//   prefetch_buffer
//   ├── prefetch_controller (this module - request generation & control)
//   ├── FIFO (storage)
//   └── OBI interface (bus protocol)
//
// RESPONSIBILITIES:
//   1. Address Generation:
//      - Sequential: PC+4 for normal prefetch
//      - Branch/Jump: Target address from IF stage
//      - Hardware loops: Loop start address
//
//   2. Request Control:
//      - Issue memory transactions when FIFO has space
//      - Track outstanding transactions (up to DEPTH)
//      - Prevent FIFO overflow
//
//   3. Response Management:
//      - Push valid responses into FIFO
//      - Flush speculative responses after branches
//      - Handle hardware loop response flushing
//
//   4. Flow Control:
//      - Backpressure based on FIFO occupancy
//      - Handshake with OBI interface
//      - Coordinate with IF stage
//
// STATE MACHINE:
//   IDLE: Normal operation
//     - Generate sequential or branch addresses
//     - Issue transactions when space available
//     - Transition to BRANCH_WAIT if branch not immediately accepted
//
//   BRANCH_WAIT: Branch target pending
//     - Replay branch address until accepted
//     - Higher priority branches can preempt
//     - Return to IDLE once accepted
//
// TRANSACTION TRACKING:
//   cnt_q: Outstanding transaction counter
//     - Increments on accepted request
//     - Decrements on received response
//     - Max value: DEPTH (FIFO depth)
//     - Prevents FIFO overflow
//
//   flush_cnt_q: Response flush counter
//     - Set to cnt_q on branch (flush speculative fetches)
//     - Decrements as responses arrive
//     - Responses discarded while flush_cnt_q > 0
//
// HARDWARE LOOP HANDLING (COREV_PULP):
//   Challenge: Loop end may not be in FIFO when loop taken
//     - Solution: Wait for loop end response, then flush wrong-path
//     - hwlp_flush_after_resp: Delayed flush pending
//     - hwlp_flush_cnt_delayed_q: Number of responses to flush
//
//   Two flush scenarios:
//     1. Loop end already in FIFO: Immediate flush
//     2. Loop end pending: Wait for response, then flush
//
// TIMING:
//   - Address selected combinationally (trans_addr_o)
//   - Requests issued when trans_valid_o & trans_ready_i
//   - Responses arrive asynchronously (resp_valid_i)
//   - FIFO push happens same cycle as response
//
// OBI MODES:
//   PULP_OBI=0: Standard OBI 1.2
//     - Multiple outstanding transactions allowed
//     - No dependency between request and response
//     - Better performance
//
//   PULP_OBI=1: Legacy PULP behavior
//     - Next request only after previous response
//     - Timing path from resp_valid to trans_req
//     - Compatibility mode
//
///////////////////////////////////////////////////////////////////////////////

module cv32e40p_prefetch_controller #(
    // Legacy PULP OBI behavior vs. standard OBI 1.2
    // 0: Standard (multiple outstanding, better performance)
    // 1: Legacy (request waits for response, timing critical)
    parameter PULP_OBI = 0,
    
    // PULP ISA Extension (hardware loops)
    // Enables special hardware loop flush handling
    parameter COREV_PULP = 1,
    
    // Prefetch FIFO Depth
    // Determines max outstanding transactions
    // Must match FIFO_DEPTH in cv32e40p_prefetch_buffer
    parameter DEPTH = 4,
    
    // FIFO Address width (calculated from DEPTH)
    // Do not override - automatically derived
    parameter FIFO_ADDR_DEPTH = (DEPTH > 1) ? $clog2(DEPTH) : 1
) (
    // ===== Clock and Reset =====
    input logic clk,
    input logic rst_n,

    // ===== Fetch Stage Control Interface =====
    // req_i: Fetch stage requests instructions
    //   - High: Continue prefetching
    //   - Low: Stall (don't issue new requests)
    input  logic        req_i,
    
    // branch_i: Branch/jump taken
    //   - Flush speculative fetches
    //   - Redirect to branch_addr_i
    input  logic        branch_i,
    
    // branch_addr_i: Branch target address
    //   - Valid only when branch_i = 1
    //   - Used for jumps, branches, exceptions
    input  logic [31:0] branch_addr_i,
    
    // busy_o: Prefetcher busy indicator
    //   - High when outstanding transactions exist
    //   - Used by controller for pipeline management
    output logic        busy_o,

    // ===== Hardware Loop Signals (COREV_PULP) =====
    // hwlp_jump_i: Hardware loop branch taken
    //   - Jump back to loop start
    //   - Lower priority than branch_i
    input logic        hwlp_jump_i,
    
    // hwlp_target_i: Hardware loop start address
    //   - Target address for loop branch
    input logic [31:0] hwlp_target_i,

    // ===== Transaction Request Interface =====
    // Interface to cv32e40p_obi_interface
    
    // trans_valid_o: Transaction request valid
    //   - Request new instruction fetch
    //   - Handshakes with trans_ready_i
    output logic trans_valid_o,
    
    // trans_ready_i: OBI interface ready
    //   - Can accept new transaction
    //   - Transaction accepted when both valid & ready
    input  logic                     trans_ready_i,
    
    // trans_addr_o: Transaction address
    //   - Address to fetch from
    //   - Valid only when trans_valid_o = 1
    //   - No stability requirements (can change)
    output logic [31:0]              trans_addr_o,

    // ===== Transaction Response Interface =====
    // Interface from cv32e40p_obi_interface
    
    // resp_valid_i: Response data valid
    //   - Instruction data arrived from memory
    //   - Consumer (FIFO) assumed always ready
    input logic resp_valid_i,

    // ===== Fetch Interface (to IF stage) =====
    // fetch_ready_i: IF stage ready to consume
    //   - Backpressure from IF stage
    input  logic fetch_ready_i,
    
    // fetch_valid_o: Valid instruction available
    //   - From FIFO or incoming response
    //   - Suppressed during branch flush
    output logic fetch_valid_o,

    // ===== FIFO Interface =====
    // Control signals to cv32e40p_fifo
    
    // fifo_push_o: Push instruction into FIFO
    //   - Asserted when valid response should be stored
    output logic fifo_push_o,
    
    // fifo_pop_o: Pop instruction from FIFO
    //   - Asserted when IF stage consumes
    output logic fifo_pop_o,
    
    // fifo_flush_o: Flush entire FIFO
    //   - On branches (discard speculative fetches)
    output logic fifo_flush_o,
    
    // fifo_flush_but_first_o: Flush all except first entry
    //   - Hardware loop optimization
    //   - Keep loop end, discard rest
    output logic                     fifo_flush_but_first_o,
    
    // fifo_cnt_i: FIFO occupancy
    //   - Number of valid entries in FIFO
    //   - Used to prevent overflow
    input logic [FIFO_ADDR_DEPTH:0] fifo_cnt_i,
    
    // fifo_empty_i: FIFO is empty
    //   - No valid entries
    input logic fifo_empty_i
);

  import cv32e40p_pkg::*;

  ///////////////////////////////////////////////////////////////////////////////
  // INTERNAL SIGNALS
  ///////////////////////////////////////////////////////////////////////////////
  
  // FSM state
  prefetch_state_e state_q, next_state;

  ///////////////////////////////////////////////////////////////////////////////
  // Transaction Counter Signals
  ///////////////////////////////////////////////////////////////////////////////
  // Tracks number of outstanding memory transactions
  
  // cnt_q: Current outstanding transaction count
  //   - Range: 0 to DEPTH
  //   - Increments on accepted request
  //   - Decrements on received response
  logic [FIFO_ADDR_DEPTH:0] cnt_q;
  
  // next_cnt: Next counter value
  //   - Calculated combinationally
  logic [FIFO_ADDR_DEPTH:0] next_cnt;
  
  // count_up: Increment counter
  //   - Request accepted (trans_valid_o & trans_ready_i)
  logic                          count_up;
  
  // count_down: Decrement counter
  //   - Response received (resp_valid_i)
  logic                          count_down;

  ///////////////////////////////////////////////////////////////////////////////
  // Response Flush Signals
  ///////////////////////////////////////////////////////////////////////////////
  // On branch, flush speculative responses still arriving from memory
  
  // flush_cnt_q: Number of responses to flush
  //   - Set to cnt_q on branch
  //   - Decrements as responses arrive and are discarded
  logic  [FIFO_ADDR_DEPTH:0]     flush_cnt_q;
  
  // next_flush_cnt: Next flush counter value
  logic [FIFO_ADDR_DEPTH:0] next_flush_cnt;

  ///////////////////////////////////////////////////////////////////////////////
  // Address Generation Signals
  ///////////////////////////////////////////////////////////////////////////////
  
  // trans_addr_q: Registered transaction address
  //   - Holds last address for replay in BRANCH_WAIT state
  logic [31:0] trans_addr_q;
  
  // trans_addr_incr: Incremented address
  //   - Current address + 4 (word increment)
  logic [31:0] trans_addr_incr;

  // aligned_branch_addr: Word-aligned branch target
  //   - Branch target with lower 2 bits forced to 00
  logic [31:0] aligned_branch_addr;

  ///////////////////////////////////////////////////////////////////////////////
  // FIFO Auxiliary Signals
  ///////////////////////////////////////////////////////////////////////////////
  
  // fifo_valid: FIFO has valid output
  //   - Equivalent to !fifo_empty_i
  logic fifo_valid;
  
  // fifo_cnt_masked: FIFO count with masking
  //   - Masked to 0 during branch (optimizes request generation)
  //   - Allows new request even if FIFO full when branching
  logic [FIFO_ADDR_DEPTH:0]      fifo_cnt_masked;

  ///////////////////////////////////////////////////////////////////////////////
  // Hardware Loop Support Signals (COREV_PULP)
  ///////////////////////////////////////////////////////////////////////////////
  // Complex logic to handle hardware loop end that may not be in FIFO yet
  
  // hwlp_wait_resp_flush: Wait for loop end response
  //   - Loop taken but loop end not yet arrived
  //   - Trigger delayed flush mechanism
  logic hwlp_wait_resp_flush;
  
  // hwlp_flush_after_resp: Delayed flush pending
  //   - Set when hwlp_wait_resp_flush triggers
  //   - Cleared after flush completes
  logic hwlp_flush_after_resp;
  
  // hwlp_flush_cnt_delayed_q: Saved flush count
  //   - Number of outstanding requests at time of loop branch
  //   - Minus 1 (for the loop end itself)
  logic [FIFO_ADDR_DEPTH:0]      hwlp_flush_cnt_delayed_q;
  
  // hwlp_flush_resp_delayed: Execute delayed flush
  //   - Asserted when loop end response arrives
  logic hwlp_flush_resp_delayed;
  
  // hwlp_flush_resp: Immediate hardware loop flush
  //   - Loop end already in FIFO or arriving this cycle
  logic hwlp_flush_resp;

  ///////////////////////////////////////////////////////////////////////////////
  // PREFETCH BUFFER STATUS
  ///////////////////////////////////////////////////////////////////////////////
  // Busy indicator for pipeline control

  // Busy if there are ongoing (or potentially outstanding) transfers
  // Used by controller to determine if prefetch buffer can be gated/flushed
  assign busy_o = (cnt_q != 3'b000) || trans_valid_o;

  ///////////////////////////////////////////////////////////////////////////////
  // IF/ID INTERFACE - FETCH VALID CONTROL
  ///////////////////////////////////////////////////////////////////////////////
  // Controls when valid instruction is presented to IF stage

  // Fectch valid control. Fetch never valid if jumping or flushing responses.
  // Fetch valid if there are instructions in FIFO or there is an incoming
  // instruction from memory.
  //
  // Suppressed when:
  //   - branch_i: Branch taken (invalidate current fetch)
  //   - flush_cnt_q > 0: Flushing speculative responses
  //
  // Valid when:
  //   - fifo_valid: FIFO has instruction
  //   - resp_valid_i: Instruction arriving from memory (fall-through)
  assign fetch_valid_o = (fifo_valid || resp_valid_i) && !(branch_i || (flush_cnt_q > 0));

  ///////////////////////////////////////////////////////////////////////////////
  // TRANSACTION REQUEST GENERATION
  ///////////////////////////////////////////////////////////////////////////////
  // Generate memory transaction requests based on FIFO space and fetch enable
  //
  // Constraints:
  //   - Only request when req_i (fetch stage wants instructions)
  //   - Never overflow FIFO: (fifo_cnt + cnt_q < DEPTH)
  //   - OBI protocol compliance (depends on PULP_OBI mode)
  //
  // Assumes: Response arrives at least 1 cycle after request

  // Prefetcher will only perform word fetches
  // Force lower 2 bits to 00 for word alignment
  assign aligned_branch_addr = {branch_addr_i[31:2], 2'b00};

  // Increment address (always word fetch)
  // Sequential prefetch: current + 4 bytes
  assign trans_addr_incr = {trans_addr_q[31:2], 2'b00} + 32'd4;

  // Transaction request generation
  generate
    if (PULP_OBI == 0) begin : gen_no_pulp_obi
      ///////////////////////////////////////////////////////////////////////////
      // Standard OBI 1.2 Mode
      ///////////////////////////////////////////////////////////////////////////
      // OBI compatible (avoids combinatorial path from instr_rvalid_i to instr_req_o).
      // Multiple trans_* transactions can be issued (and accepted) before a response
      // (resp_*) is received.
      //
      // Benefits:
      //   - Better performance (multiple outstanding)
      //   - No timing critical path
      //   - True pipelining of requests
      
      assign trans_valid_o = req_i && (fifo_cnt_masked + cnt_q < DEPTH);
      
    end else begin : gen_pulp_obi
      ///////////////////////////////////////////////////////////////////////////
      // Legacy PULP OBI Mode
      ///////////////////////////////////////////////////////////////////////////
      // Legacy PULP OBI behavior, i.e. only issue subsequent transaction if preceding transfer
      // is about to finish (re-introducing timing critical path from instr_rvalid_i to instr_req_o)
      //
      // Drawbacks:
      //   - Lower performance (serialized requests)
      //   - Timing critical path (resp_valid → trans_req)
      //   - Maintained for legacy compatibility only
      
      assign trans_valid_o = (cnt_q == 3'b000) ? req_i && (fifo_cnt_masked + cnt_q < DEPTH) :
                                                 req_i && (fifo_cnt_masked + cnt_q < DEPTH) && resp_valid_i;
    end
  endgenerate

  ///////////////////////////////////////////////////////////////////////////////
  // FIFO COUNT MASKING OPTIMIZATION
  ///////////////////////////////////////////////////////////////////////////////
  // Optimization:
  // fifo_cnt is used to understand if we can perform new memory requests
  // When branching, we flush both the FIFO and the outstanding requests. Therefore,
  // there is surely space for a new request.
  // Masking fifo_cnt in this case allows for making a new request when the FIFO
  // is not empty and we are jumping, and (fifo_cnt_i + cnt_q == DEPTH)
  //
  // Effect: Enables immediate request on branch even if FIFO+cnt appears full
  
  assign fifo_cnt_masked = (branch_i || hwlp_jump_i) ? '0 : fifo_cnt_i;

  ///////////////////////////////////////////////////////////////////////////////
  // FSM: ADDRESS GENERATION AND STATE CONTROL
  ///////////////////////////////////////////////////////////////////////////////
  // Controls OBI A channel (request) signals
  // Two states: IDLE (normal) and BRANCH_WAIT (branch not yet accepted)

  // FSM (state_q, next_state) to control OBI A channel signals.
  always_comb begin
    next_state   = state_q;
    trans_addr_o = trans_addr_q;

    case (state_q)
      ///////////////////////////////////////////////////////////////////////////
      // IDLE State: Normal Operation
      ///////////////////////////////////////////////////////////////////////////
      // Default state (pass on branch target address or transaction with incremented address)
      IDLE: begin
        begin
          if (branch_i) begin
            ///////////////////////////////////////////////////////////////////
            // Branch/Jump: Highest Priority
            ///////////////////////////////////////////////////////////////////
            // Jumps must have the highest priority (e.g. an interrupt must
            // have higher priority than a HW-loop branch)
            trans_addr_o = aligned_branch_addr;
            
          end else if (hwlp_jump_i) begin
            ///////////////////////////////////////////////////////////////////
            // Hardware Loop: Medium Priority
            ///////////////////////////////////////////////////////////////////
            // Jump to loop start address
            trans_addr_o = hwlp_target_i;
            
          end else begin
            ///////////////////////////////////////////////////////////////////
            // Sequential Fetch: Normal Case
            ///////////////////////////////////////////////////////////////////
            // Increment by 4 (word)
            trans_addr_o = trans_addr_incr;
          end
        end
        
        if ((branch_i || hwlp_jump_i) && !(trans_valid_o && trans_ready_i)) begin
          ///////////////////////////////////////////////////////////////////
          // Transition to BRANCH_WAIT
          ///////////////////////////////////////////////////////////////////
          // Taken branch, but transaction not yet accepted by bus interface adapter.
          // Must replay address next cycle
          next_state = BRANCH_WAIT;
        end
      end  // case: IDLE

      ///////////////////////////////////////////////////////////////////////////
      // BRANCH_WAIT State: Replaying Branch Address
      ///////////////////////////////////////////////////////////////////////////
      BRANCH_WAIT: begin
        // Replay previous branch target address (trans_addr_q) or new branch address (this can
        // occur if for example an interrupt is taken right after a taken jump which did not
        // yet have its target address accepted by the bus interface adapter.
        //
        // Priority: New branch (interrupt) can preempt old branch
        trans_addr_o = branch_i ? aligned_branch_addr : trans_addr_q;
        
        if (trans_valid_o && trans_ready_i) begin
          // Transaction with branch target address has been accepted. Start regular prefetch again.
          next_state = IDLE;
        end
      end  // case: BRANCH_WAIT
    endcase
  end

  ///////////////////////////////////////////////////////////////////////////////
  // FIFO MANAGEMENT
  ///////////////////////////////////////////////////////////////////////////////
  // Controls when responses are pushed into FIFO vs. discarded

  // Pass on response transfer directly to FIFO (which should be ready, otherwise
  // the corresponding transfer would not have been requested via trans_valid_o).
  // Upon a branch (branch_i) all incoming responses (resp_valid_i) are flushed
  // until the flush count is 0 again. (The flush count is initialized with the
  // number of outstanding transactions at the time of the branch).
  
  // fifo_valid: FIFO has output data
  assign fifo_valid = !fifo_empty_i;
  
  // fifo_push_o: Push response into FIFO
  //   Conditions:
  //     - resp_valid_i: Response arrived
  //     - (fifo_valid || !fetch_ready_i): FIFO has data OR IF stage not ready
  //         (forces buffering in FIFO rather than fall-through)
  //     - NOT (branch_i || flush_cnt_q > 0): Not flushing
  assign fifo_push_o = resp_valid_i && (fifo_valid || !fetch_ready_i) && !(branch_i || (flush_cnt_q > 0));
  
  // fifo_pop_o: Pop instruction from FIFO
  //   When IF stage ready and FIFO has data
  assign fifo_pop_o = fifo_valid && fetch_ready_i;

  ///////////////////////////////////////////////////////////////////////////////
  // OUTSTANDING TRANSACTION COUNTER
  ///////////////////////////////////////////////////////////////////////////////
  // Counter (cnt_q, next_cnt) to count number of outstanding OBI transactions
  // (maximum = DEPTH)
  //
  // Counter overflow is prevented by limiting the number of outstanding transactions
  // to DEPTH. Counter underflow is prevented by the assumption that resp_valid_i = 1
  // will only occur in response to accepted transfer request (as per the OBI protocol).

  // Count up: Increment upon accepted transfer request
  assign count_up = trans_valid_o && trans_ready_i;
  
  // Count down: Decrement upon accepted transfer response
  assign count_down = resp_valid_i;

  // Next count calculation
  always_comb begin
    case ({
      count_up, count_down
    })
      2'b00: begin
        // No change
        next_cnt = cnt_q;
      end
      2'b01: begin
        // Response only: decrement
        next_cnt = cnt_q - 1'b1;
      end
      2'b10: begin
        // Request only: increment
        next_cnt = cnt_q + 1'b1;
      end
      2'b11: begin
        // Request and response: no change
        next_cnt = cnt_q;
      end
    endcase
  end

  ///////////////////////////////////////////////////////////////////////////////
  // HARDWARE LOOP FLUSH CONTROL (COREV_PULP)
  ///////////////////////////////////////////////////////////////////////////////
  // Complex logic to handle loop end instruction that may not be in FIFO yet

  generate
    if (COREV_PULP) begin : gen_hwlp

      ///////////////////////////////////////////////////////////////////////////
      // FIFO Flush Control for Hardware Loops
      ///////////////////////////////////////////////////////////////////////////
      // Flush the FIFO if it is not empty and we are hwlp branching.
      // If HWLP_END is not going to ID, save it from the flush.
      // Don't flush the FIFO if it is empty (maybe we must accept
      // HWLP_end from the memory in this cycle)
      //
      // Two flush types:
      //   1. fifo_flush_o: Flush all (HWLP_END going to ID this cycle)
      //   2. fifo_flush_but_first_o: Keep first (HWLP_END staying in FIFO)
      
      assign fifo_flush_o           = branch_i || (hwlp_jump_i && !fifo_empty_i && fifo_pop_o);
      assign fifo_flush_but_first_o = (hwlp_jump_i && !fifo_empty_i && !fifo_pop_o);

      ///////////////////////////////////////////////////////////////////////////
      // HWLP Main Response Flush Controller
      ///////////////////////////////////////////////////////////////////////////
      // If HWLP_END-4 is in ID and HWLP_END is being/was returned by the memory
      // we can flush all the eventual outstanding requests up to now
      //
      // Immediate flush: Loop end already available
      
      assign hwlp_flush_resp        = hwlp_jump_i && !(fifo_empty_i && !resp_valid_i);

      ///////////////////////////////////////////////////////////////////////////
      // HWLP Delayed Flush Controller
      ///////////////////////////////////////////////////////////////////////////
      // If HWLP_END-4 is in ID and HWLP_END has not been returned yet,
      // save the present number of outstanding requests (subtract the HWLP_END one).
      // Wait for HWLP_END then flush the saved number of (wrong) outstanding requests
      //
      // Delayed flush: Loop end not yet arrived from memory
      
      assign hwlp_wait_resp_flush   = hwlp_jump_i && (fifo_empty_i && !resp_valid_i);

      // Delayed flush state machine
      always_ff @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
          hwlp_flush_after_resp    <= 1'b0;
          hwlp_flush_cnt_delayed_q <= 2'b00;
        end else begin
          if (branch_i) begin
            ///////////////////////////////////////////////////////////////////
            // Interrupt Preemption
            ///////////////////////////////////////////////////////////////////
            // Reset the flush request if an interrupt is taken
            // Interrupt has higher priority than hardware loop
            hwlp_flush_after_resp    <= 1'b0;
            hwlp_flush_cnt_delayed_q <= 2'b00;
          end else begin
            if (hwlp_wait_resp_flush) begin
              ///////////////////////////////////////////////////////////////
              // Trigger Delayed Flush
              ///////////////////////////////////////////////////////////////
              hwlp_flush_after_resp    <= 1'b1;
              // cnt_q > 0 checked by an assertion
              // Subtract 1 for the loop end instruction itself
              hwlp_flush_cnt_delayed_q <= cnt_q - 1'b1;
            end else begin
              ///////////////////////////////////////////////////////////////
              // Complete Delayed Flush
              ///////////////////////////////////////////////////////////////
              // Reset the delayed flush request when it's completed
              if (hwlp_flush_resp_delayed) begin
                hwlp_flush_after_resp    <= 1'b0;
                hwlp_flush_cnt_delayed_q <= 2'b00;
              end
            end
          end
        end
      end

      // This signal is masked by branch_i in the flush counter process,
      // because if an interrupt occurs during a delayed flush, the interrupt
      // is served first so the flush should be normal (caused by branch_i)
      assign hwlp_flush_resp_delayed = hwlp_flush_after_resp && resp_valid_i;

    end else begin : gen_no_hwlp

      ///////////////////////////////////////////////////////////////////////////
      // No Hardware Loop Support
      ///////////////////////////////////////////////////////////////////////////
      // Tie off all hardware loop signals
      
      // Flush the FIFO if it is not empty
      assign fifo_flush_o             = branch_i;
      assign fifo_flush_but_first_o   = 1'b0;
      assign hwlp_flush_resp          = 1'b0;
      assign hwlp_wait_resp_flush     = 1'b0;

      assign hwlp_flush_after_resp    = 1'b0;
      assign hwlp_flush_cnt_delayed_q = 2'b00;
      assign hwlp_flush_resp_delayed  = 1'b0;


    end
  endgenerate

  ///////////////////////////////////////////////////////////////////////////////
  // RESPONSE FLUSH COUNTER
  ///////////////////////////////////////////////////////////////////////////////
  // Counter (flush_cnt_q, next_flush_cnt) to count reseponses to be flushed.
  // When a branch occurs, outstanding responses are speculative and must be discarded.

  always_comb begin
    next_flush_cnt = flush_cnt_q;

    // Number of outstanding transfers at time of branch equals the number of
    // responses that will need to be flushed (responses already in the FIFO will
    // be flushed there)
    if (branch_i || hwlp_flush_resp) begin
      ///////////////////////////////////////////////////////////////////////////
      // Branch or HW Loop Immediate Flush
      ///////////////////////////////////////////////////////////////////////////
      // Set flush count to current outstanding count
      next_flush_cnt = cnt_q;
      
      if (resp_valid_i && (cnt_q > 0)) begin
        // Response arriving same cycle as branch: flush it and decrement
        next_flush_cnt = cnt_q - 1'b1;
      end
      
    end else if (hwlp_flush_resp_delayed) begin
      ///////////////////////////////////////////////////////////////////////////
      // HW Loop Delayed Flush
      ///////////////////////////////////////////////////////////////////////////
      // Delayed flush has a lower priority than the normal flush,
      // because HW loops branches have lower priority than
      // taken interrupts
      next_flush_cnt = hwlp_flush_cnt_delayed_q;
      
    end else if (resp_valid_i && (flush_cnt_q > 0)) begin
      ///////////////////////////////////////////////////////////////////////////
      // Decrement Flush Counter
      ///////////////////////////////////////////////////////////////////////////
      // Response arrived while flushing: discard and decrement counter
      next_flush_cnt = flush_cnt_q - 1'b1;
    end
  end

  ///////////////////////////////////////////////////////////////////////////////
  // REGISTERS
  ///////////////////////////////////////////////////////////////////////////////
  // Sequential logic for state and counters

  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      // Reset all state
      state_q      <= IDLE;
      cnt_q        <= '0;
      flush_cnt_q  <= '0;
      trans_addr_q <= '0;
    end else begin
      // Update state
      state_q     <= next_state;
      cnt_q       <= next_cnt;
      flush_cnt_q <= next_flush_cnt;
      
      // Update address on branch or accepted transaction
      if (branch_i || hwlp_jump_i || (trans_valid_o && trans_ready_i)) begin
        trans_addr_q <= trans_addr_o;
      end
    end
  end

endmodule  // cv32e40p_prefetch_controller
