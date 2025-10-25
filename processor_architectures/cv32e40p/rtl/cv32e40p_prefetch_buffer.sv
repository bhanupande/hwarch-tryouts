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
// Engineer:       Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Design Name:    Prefetcher Buffer for 32 bit memory interface              //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Prefetch Buffer that caches instructions. This cuts overly //
//                 long critical paths to the instruction cache               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Module: cv32e40p_prefetch_buffer
///////////////////////////////////////////////////////////////////////////////
//
// FUNCTION:
//   Instruction prefetch buffer with FIFO storage.
//   Decouples instruction fetch timing from IF stage timing.
//   Integrates prefetch controller, FIFO, and OBI interface.
//
// ARCHITECTURE:
//   cv32e40p_prefetch_buffer (this module - integration wrapper)
//   ├── cv32e40p_prefetch_controller (FSM - controls prefetching)
//   ├── cv32e40p_fifo (storage - buffers prefetched instructions)
//   └── cv32e40p_obi_interface (protocol adapter - memory interface)
//
// WHY PREFETCH?
//   Benefits:
//     1. Performance: Hides memory latency for sequential fetches
//     2. Timing: Breaks critical path from memory to decode
//     3. Throughput: Allows back-to-back instruction delivery
//     4. Efficiency: Amortizes memory interface overhead
//
//   Without prefetch:
//     - Every instruction waits for memory roundtrip
//     - ID stage stalls on every fetch
//     - Poor IPC (Instructions Per Cycle)
//
//   With prefetch:
//     - FIFO absorbs memory latency bubbles
//     - ID stage sees continuous instruction stream
//     - Better IPC, especially for sequential code
//
// FIFO OPERATION:
//   Depth: FIFO_DEPTH = 2 (default)
//     - Minimum 2 for hardware loop correctness
//     - Deeper FIFO → better performance but more area
//     - Can hide up to FIFO_DEPTH memory latency cycles
//
//   Push: New instructions from memory enter FIFO
//   Pop: IF stage consumes instructions from FIFO
//   Flush: Branches invalidate FIFO contents
//
// FALL-THROUGH PATH:
//   When FIFO empty and instruction arrives:
//     - Bypass FIFO directly to IF stage
//     - Saves one cycle latency
//     - Critical for branch target fetch
//
// BRANCH HANDLING:
//   On branch:
//     1. Flush FIFO (invalidate sequential prefetches)
//     2. Send new address to memory
//     3. Wait for branch target instruction
//     4. Resume prefetching from new PC
//
// HARDWARE LOOP SUPPORT (COREV_PULP=1):
//   Zero-overhead loops need special handling:
//     - hwlp_jump_i: Loop back detected
//     - hwlp_target_i: Loop start address
//     - FIFO may already contain loop body
//     - Avoid re-fetching if already buffered
//
// OBI PROTOCOL:
//   Request phase: trans_valid/ready handshake
//   Response phase: resp_valid indicates data arrival
//   Multiple outstanding requests: Up to FIFO_DEPTH
//
// TIMING:
//   Address sent one cycle before data arrives
//   FIFO provides elastic buffer for timing closure
//   Fall-through path bypasses FIFO for min latency
//
///////////////////////////////////////////////////////////////////////////////

// input port: send address one cycle before the data
// clear_i clears the FIFO for the following cycle. in_addr_i can be sent in
// this cycle already

module cv32e40p_prefetch_buffer #(
    // Legacy PULP OBI behavior vs. standard OBI 1.2
    // 0: Standard OBI (trans_* stable during stalls)
    // 1: PULP legacy (trans_* can change, less hardware)
    parameter PULP_OBI = 0,
    
    // PULP ISA extensions enable (hardware loops)
    // Required for hwlp_jump_i/hwlp_target_i support
    parameter COREV_PULP = 1
) (
    // ===== Clock and Reset =====
    input logic clk,
    input logic rst_n,

    // ===== Control from IF Stage =====
    // req_i: IF stage requesting instruction
    //   - High: Continue fetching
    //   - Low: Pause (stall)
    input logic        req_i,

    // ===== Branch Control =====
    // branch_i: Branch/jump taken, flush FIFO
    //   - Invalidates sequential prefetches
    //   - Redirects prefetch to branch_addr_i
    input logic        branch_i,
    
    // branch_addr_i: Target address of branch/jump
    //   - Used when branch_i asserted
    //   - Must be word-aligned (RISC-V requirement)
    input logic [31:0] branch_addr_i,

    // ===== Hardware Loop Support (COREV_PULP) =====
    // hwlp_jump_i: Zero-overhead loop back taken
    //   - Similar to branch but for HW loops
    //   - May reuse already-buffered instructions
    input logic        hwlp_jump_i,
    
    // hwlp_target_i: Loop start address
    //   - Jump target for hardware loop
    input logic [31:0] hwlp_target_i,

    // ===== Handshake with IF Stage =====
    // fetch_ready_i: IF stage ready to accept instruction
    //   - Backpressure from IF stage
    //   - When low, prefetch buffer stalls output
    input  logic        fetch_ready_i,
    
    // fetch_valid_o: Valid instruction available
    //   - IF stage can consume fetch_rdata_o
    //   - Qualified by req_i
    output logic        fetch_valid_o,
    
    // fetch_rdata_o: Instruction data to IF stage
    //   - From FIFO or fall-through from memory
    //   - Valid when fetch_valid_o high
    output logic [31:0] fetch_rdata_o,

    // ===== Instruction Memory Interface (OBI) =====
    // instr_req_o: Request instruction from memory
    //   - Driven by prefetch controller
    //   - May have multiple outstanding requests
    output logic        instr_req_o,
    
    // instr_gnt_i: Memory grants request
    //   - Handshake with instr_req_o
    //   - Data arrives when instr_rvalid_i high
    input  logic        instr_gnt_i,
    
    // instr_addr_o: Address of requested instruction
    //   - Word-aligned (bits [1:0] = 2'b00)
    //   - Increments for sequential fetches
    output logic [31:0] instr_addr_o,
    
    // instr_rdata_i: Instruction data from memory
    //   - Valid when instr_rvalid_i high
    //   - Goes to FIFO or fall-through to IF stage
    input  logic [31:0] instr_rdata_i,
    
    // instr_rvalid_i: Instruction data valid
    //   - Data on instr_rdata_i is valid
    //   - Response phase of OBI transaction
    input  logic        instr_rvalid_i,
    
    // instr_err_i: Bus error during fetch
    //   - Not yet used (reserved for future)
    //   - Would signal instruction access fault
    input  logic        instr_err_i,
    
    // instr_err_pmp_i: PMP (Physical Memory Protection) error
    //   - Not yet used (reserved for future)
    //   - Would signal PMP violation on instruction fetch
    input  logic        instr_err_pmp_i,

    // ===== Status Output =====
    // Prefetch Buffer Status
    output logic busy_o
);

  ///////////////////////////////////////////////////////////////////////////////
  // LOCAL PARAMETERS
  ///////////////////////////////////////////////////////////////////////////////
  
  // FIFO_DEPTH: Number of instruction slots in prefetch FIFO
  //   - Default: 2 entries (minimum for correctness)
  //   - Must be greater than 1 (assertion in prefetch_controller)
  //   - Must be power of 2 (due to FIFO address pointer wraparound)
  //   - Also controls max outstanding memory requests
  //
  // Why minimum 2?
  //   - Hardware loops require 2+ entries to avoid stalls
  //   - Single entry causes back-to-back fetch stalls
  //   - Verified by a_fifo_depth assertion below
  //
  // Performance tuning:
  //   - Depth 2: Minimal (current setting, adequate for most)
  //   - Depth 3+: Reduces stalls vs. master branch behavior
  //   - Depth 4+: Better for high-latency or variable-latency memory
  localparam FIFO_DEPTH = 2;
  
  // FIFO_ADDR_DEPTH: Address width for FIFO pointers
  //   - Calculated as log2(FIFO_DEPTH)
  //   - For FIFO_DEPTH=2: FIFO_ADDR_DEPTH=1 (1-bit pointer)
  //   - For FIFO_DEPTH=4: FIFO_ADDR_DEPTH=2 (2-bit pointer)
  localparam int unsigned FIFO_ADDR_DEPTH = $clog2(FIFO_DEPTH);

  ///////////////////////////////////////////////////////////////////////////////
  // INTERNAL SIGNALS - Transaction Request Interface
  ///////////////////////////////////////////////////////////////////////////////
  
  // Transaction request between prefetch_controller and obi_interface
  // This is an internal protocol for requesting memory transactions
  
  // trans_valid: Controller wants to issue transaction
  //   - Driven by cv32e40p_prefetch_controller
  //   - Handshakes with trans_ready
  logic                     trans_valid;
  
  // trans_ready: OBI interface can accept transaction
  //   - Driven by cv32e40p_obi_interface
  //   - When both trans_valid & trans_ready: transaction accepted
  logic                     trans_ready;
  
  // trans_addr: Address for transaction request
  //   - Points to instruction to fetch
  //   - Word-aligned (lower 2 bits typically 0)
  logic [             31:0] trans_addr;

  ///////////////////////////////////////////////////////////////////////////////
  // INTERNAL SIGNALS - FIFO Control
  ///////////////////////////////////////////////////////////////////////////////
  
  // fifo_flush: Invalidate all FIFO contents
  //   - Asserted on branches, exceptions
  //   - Clears all buffered instructions
  logic                     fifo_flush;
  
  // fifo_flush_but_first: Flush FIFO except first entry
  //   - Special case for certain control flow
  //   - Preserves one valid instruction
  logic                     fifo_flush_but_first;
  
  // fifo_cnt: Current FIFO occupancy
  //   - Range: 0 to FIFO_DEPTH (inclusive)
  //   - Width: FIFO_ADDR_DEPTH+1 to represent full count
  //   - Used by controller to track available slots
  logic [FIFO_ADDR_DEPTH:0] fifo_cnt;

  ///////////////////////////////////////////////////////////////////////////////
  // INTERNAL SIGNALS - FIFO Data Path
  ///////////////////////////////////////////////////////////////////////////////
  
  // fifo_rdata: Instruction data from FIFO output
  //   - Read from FIFO when fifo_pop asserted
  //   - Goes to fetch_rdata_o (unless fall-through active)
  logic [             31:0] fifo_rdata;
  
  // fifo_push: Push new instruction into FIFO
  //   - Asserted when resp_valid and space available
  //   - Stores resp_rdata into FIFO
  logic                     fifo_push;
  
  // fifo_pop: Pop instruction from FIFO
  //   - Asserted when IF stage consumes instruction
  //   - Advances FIFO read pointer
  logic                     fifo_pop;
  
  // fifo_empty: FIFO has no valid entries
  //   - Enables fall-through path
  //   - Prevents invalid pops
  logic                     fifo_empty;

  ///////////////////////////////////////////////////////////////////////////////
  // INTERNAL SIGNALS - Transaction Response Interface
  ///////////////////////////////////////////////////////////////////////////////
  
  // Transaction response between obi_interface and FIFO
  // Carries instruction data back from memory
  
  // resp_valid: Memory response arrived
  //   - Driven by cv32e40p_obi_interface (from instr_rvalid_i)
  //   - Qualifies resp_rdata
  logic                     resp_valid;
  
  // resp_rdata: Instruction data from memory response
  //   - Valid when resp_valid high
  //   - Either pushed to FIFO or falls through to output
  logic [             31:0] resp_rdata;
  
  // resp_err: Bus error on memory response
  //   - Not currently used (future feature)
  //   - Would indicate instruction access fault
  logic                     resp_err;

  ///////////////////////////////////////////////////////////////////////////////
  // COMPONENT INSTANTIATIONS
  ///////////////////////////////////////////////////////////////////////////////
  
  //////////////////////////////////////////////////////////////////////////////
  // Prefetch Controller: FSM managing prefetch logic
  //////////////////////////////////////////////////////////////////////////////
  // Responsibilities:
  //   1. Generate sequential fetch addresses (PC+4)
  //   2. Handle branch/jump redirection
  //   3. Track FIFO fullness, throttle requests
  //   4. Manage hardware loop address handling
  //   5. Provide busy status to core controller

  cv32e40p_prefetch_controller #(
      .DEPTH     (FIFO_DEPTH),
      .PULP_OBI  (PULP_OBI),
      .COREV_PULP(COREV_PULP)
  ) prefetch_controller_i (
      // Clock and reset
      .clk  (clk),
      .rst_n(rst_n),

      // Control from IF stage
      .req_i        (req_i),           // IF stage requesting instruction
      .branch_i     (branch_i),        // Branch taken
      .branch_addr_i(branch_addr_i),   // Branch target
      .busy_o       (busy_o),          // Prefetch busy status

      // Hardware loop support
      .hwlp_jump_i  (hwlp_jump_i),     // HW loop jump
      .hwlp_target_i(hwlp_target_i),   // HW loop target

      // Transaction request to OBI interface
      .trans_valid_o(trans_valid),     // Request transaction
      .trans_ready_i(trans_ready),     // OBI ready
      .trans_addr_o (trans_addr),      // Address to fetch

      // Response from OBI interface
      .resp_valid_i(resp_valid),       // Memory response arrived

      // Handshake with IF stage
      .fetch_ready_i(fetch_ready_i),   // IF ready to accept
      .fetch_valid_o(fetch_valid_o),   // Valid instruction available

      // FIFO control and status
      .fifo_push_o           (fifo_push),            // Push to FIFO
      .fifo_pop_o            (fifo_pop),             // Pop from FIFO
      .fifo_flush_o          (fifo_flush),           // Flush all
      .fifo_flush_but_first_o(fifo_flush_but_first), // Flush except first
      .fifo_cnt_i            (fifo_cnt),             // FIFO occupancy
      .fifo_empty_i          (fifo_empty)            // FIFO empty status
  );

  //////////////////////////////////////////////////////////////////////////////
  // Instruction FIFO: 2-deep buffer for prefetched instructions
  //////////////////////////////////////////////////////////////////////////////
  // Responsibilities:
  //   1. Store up to FIFO_DEPTH instructions
  //   2. Provide elastic buffering between memory and IF stage
  //   3. Support flush operations (all or all-but-first)
  //   4. Track occupancy for controller throttling
  //
  // Configuration:
  //   - FALL_THROUGH=0: Data goes through FIFO registers (1 cycle)
  //     (Fall-through optimization handled externally by mux)
  //   - DATA_WIDTH=32: Full 32-bit instructions
  //   - DEPTH=FIFO_DEPTH: Configurable depth (default 2)

  cv32e40p_fifo #(
      .FALL_THROUGH(1'b0),         // No internal fall-through
      .DATA_WIDTH  (32),           // 32-bit instructions
      .DEPTH       (FIFO_DEPTH)    // 2 entries (default)
  ) fifo_i (
      // Clock and reset
      .clk_i            (clk),
      .rst_ni           (rst_n),
      
      // Flush controls
      .flush_i          (fifo_flush),            // Flush all entries
      .flush_but_first_i(fifo_flush_but_first),  // Flush all but first
      
      // Test mode (unused)
      .testmode_i       (1'b0),
      
      // Status outputs
      .full_o           (),              // Full flag (unused)
      .empty_o          (fifo_empty),    // Empty flag
      .cnt_o            (fifo_cnt),      // Current count
      
      // Push interface (from memory response)
      .data_i           (resp_rdata),    // Instruction data
      .push_i           (fifo_push),     // Write enable
      
      // Pop interface (to fall-through mux)
      .data_o           (fifo_rdata),    // Instruction output
      .pop_i            (fifo_pop)       // Read enable
  );

  //////////////////////////////////////////////////////////////////////////////
  // FALL-THROUGH PATH: Bypass FIFO for minimum latency
  //////////////////////////////////////////////////////////////////////////////
  // When FIFO is empty and instruction arrives, bypass directly to output.
  // This saves one cycle on cache hits or branch targets.
  //
  // Operation:
  //   - fifo_empty=1: Use resp_rdata (direct from memory)
  //   - fifo_empty=0: Use fifo_rdata (normal buffered path)
  //
  // Why not use FIFO's internal fall-through?
  //   - Simpler control logic with external mux
  //   - Clearer separation of concerns
  //   - Easier timing closure

  // First POP from the FIFO if it is not empty.
  // Otherwise, try to fall-through it.
  assign fetch_rdata_o = fifo_empty ? resp_rdata : fifo_rdata;

  //////////////////////////////////////////////////////////////////////////////
  // OBI Interface: Protocol adapter for instruction memory
  //////////////////////////////////////////////////////////////////////////////
  // Responsibilities:
  //   1. Convert internal transaction interface to OBI protocol
  //   2. Handle OBI request/grant/valid handshakes
  //   3. Track outstanding requests
  //   4. Provide response interface to FIFO
  //
  // Configuration:
  //   - TRANS_STABLE=0: trans_* signals NOT stable during waits
  //     * Reduces hardware (no holding registers)
  //     * Required for hardware loops to work correctly
  //     * Ignored in legacy PULP_OBI mode (not OBI 1.2 compliant)
  //     * DO NOT CHANGE - HWLP depends on this!

  cv32e40p_obi_interface #(
      .TRANS_STABLE(0)  // CRITICAL: Keep at 0 for HWLP correctness!
                        // trans_* NOT guaranteed stable during waited transfers
                        // Ignored for legacy PULP behavior (PULP_OBI=1)
  )
  instruction_obi_i
  (
      // Clock and reset
      .clk  (clk),
      .rst_n(rst_n),

      // Internal transaction request interface
      .trans_valid_i(trans_valid),              // Controller requests transaction
      .trans_ready_o(trans_ready),              // OBI ready to accept
      .trans_addr_i ({trans_addr[31:2], 2'b00}), // Word-aligned address
      .trans_we_i   (1'b0),                     // Read-only (instruction fetch)
      .trans_be_i   (4'b1111),                  // Byte enables (unused for reads)
      .trans_wdata_i(32'b0),                    // Write data (unused)
      .trans_atop_i (6'b0),                     // Atomic operations (not used)

      // Internal transaction response interface
      .resp_valid_o(resp_valid),                // Response valid
      .resp_rdata_o(resp_rdata),                // Instruction data
      .resp_err_o  (resp_err),                  // Bus error (currently unused)

      // External OBI bus signals
      .obi_req_o   (instr_req_o),               // Memory request
      .obi_gnt_i   (instr_gnt_i),               // Memory grant
      .obi_addr_o  (instr_addr_o),              // Memory address
      .obi_we_o    (),                          // Unconnected (read-only)
      .obi_be_o    (),                          // Unconnected (not used for I-fetch)
      .obi_wdata_o (),                          // Unconnected (read-only)
      .obi_atop_o  (),                          // Unconnected (no atomics)
      .obi_rdata_i (instr_rdata_i),             // Instruction data from memory
      .obi_rvalid_i(instr_rvalid_i),            // Data valid from memory
      .obi_err_i   (instr_err_i)                // Bus error from memory
  );

  ///////////////////////////////////////////////////////////////////////////////
  // ASSERTIONS
  ///////////////////////////////////////////////////////////////////////////////
  // Design correctness checks (enabled with CV32E40P_ASSERT_ON)

`ifdef CV32E40P_ASSERT_ON

  //////////////////////////////////////////////////////////////////////////////
  // Assertion: FIFO depth must be > 1 for hardware loops
  //////////////////////////////////////////////////////////////////////////////
  // FIFO_DEPTH must be greater than 1. Otherwise, the property
  // p_hwlp_end_already_gnt_when_hwlp_branch in cv32e40p_prefetch_controller
  // is not verified, since the prefetcher cannot ask for HWLP_END the cycle
  // in which HWLP_END-4 is being absorbed by ID.
  //
  // Explanation:
  //   Hardware loops need to buffer the loop-end instruction while the
  //   loop-start instruction is being fetched. With FIFO_DEPTH=1, there's
  //   no room to hold both, causing correctness issues.
  //
  // Minimum: FIFO_DEPTH = 2

  property p_fifo_depth_gt_1;
    @(posedge clk) (FIFO_DEPTH > 1);
  endproperty

  a_fifo_depth_gt_1 :
  assert property (p_fifo_depth_gt_1);

  //////////////////////////////////////////////////////////////////////////////
  // Assertion: Branch target must be halfword-aligned (RV32C support)
  //////////////////////////////////////////////////////////////////////////////
  // With compressed instruction extension (RV32C), instructions can be:
  //   - 32-bit (word-aligned): Address[1:0] = 2'b00
  //   - 16-bit (halfword-aligned): Address[1:0] = 2'b10
  //
  // Minimum alignment: halfword (bit [0] = 0)
  // This assertion checks bit [0] only, allowing both alignments.

  // Check that branch target address is half-word aligned (RV32-C)
  property p_branch_halfword_aligned;
    @(posedge clk) (branch_i) |-> (branch_addr_i[0] == 1'b0);
  endproperty

  a_branch_halfword_aligned :
  assert property (p_branch_halfword_aligned);

  //////////////////////////////////////////////////////////////////////////////
  // Assertion: Memory interface address must be word-aligned
  //////////////////////////////////////////////////////////////////////////////
  // The OBI bus always fetches full 32-bit words.
  // Even with RV32C, memory interface uses word-aligned addresses.
  // Aligner module extracts 16-bit chunks as needed.
  //
  // This is ALWAYS true (1'b1 antecedent), not just during requests.

  // Check that bus interface transactions are word aligned
  property p_instr_addr_word_aligned;
    @(posedge clk) (1'b1) |-> (instr_addr_o[1:0] == 2'b00);
  endproperty

  a_instr_addr_word_aligned :
  assert property (p_instr_addr_word_aligned);

  //////////////////////////////////////////////////////////////////////////////
  // Assertion: Branch requires active fetch request
  //////////////////////////////////////////////////////////////////////////////
  // A taken branch can only occur if the IF stage is actively fetching.
  // branch_i implies req_i must be high.

  // Check that a taken branch can only occur if fetching is requested
  property p_branch_implies_req;
    @(posedge clk) (branch_i) |-> (req_i);
  endproperty

  a_branch_implies_req :
  assert property (p_branch_implies_req);

  //////////////////////////////////////////////////////////////////////////////
  // Assertion: Branch invalidates FIFO output in same cycle
  //////////////////////////////////////////////////////////////////////////////
  // When a branch is taken, the FIFO output must not be accepted by IF stage.
  // This ensures sequential prefetches are discarded immediately.

  // Check that after a taken branch the initial FIFO output is not accepted
  property p_branch_invalidates_fifo;
    @(posedge clk) (branch_i) |-> (!(fetch_valid_o && fetch_ready_i));
  endproperty

  a_branch_invalidates_fifo :
  assert property (p_branch_invalidates_fifo);

  //////////////////////////////////////////////////////////////////////////////
  // Future Feature: Bus Error & PMP Support
  //////////////////////////////////////////////////////////////////////////////
  // External instruction bus errors are not supported yet. PMP errors are not supported yet.
  //
  // Note: Once PMP is re-introduced please consider to make instr_err_pmp_i a 'data' signal
  // that is qualified with instr_req_o && instr_gnt_i (instead of suppressing instr_gnt_i
  // as is currently done. This will keep the instr_req_o/instr_gnt_i protocol intact.
  //
  // WARNING: JUST RE-ENABLING the PMP VIA ITS USE_PMP LOCALPARAM WILL NOT WORK BECAUSE OF
  // THE GRANT SUPPRESSION IN THE PMP.
  //
  // TODO for PMP re-enablement:
  //   1. Make instr_err_pmp_i a data signal (not control signal)
  //   2. Qualify with instr_req_o && instr_gnt_i handshake
  //   3. Remove grant suppression in PMP logic
  //   4. Update error handling in prefetch controller
  //   5. Add exception generation in IF/ID stages
  //   6. Test with various PMP configurations

  property p_no_error;
    @(posedge clk) (1'b1) |-> ((instr_err_i == 1'b0) && (instr_err_pmp_i == 1'b0));
  endproperty

  a_no_error :
  assert property (p_no_error);




`endif

endmodule  // cv32e40p_prefetch_buffer
