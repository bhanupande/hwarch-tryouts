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
// Engineer:       Lukas Mueller - lukasmue@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    APU (Auxiliary Processing Unit) Dispatcher                 //
// Project Name:   PULP / CV32E40P                                            //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Dispatcher for offloading instructions to coprocessors     //
//                                                                            //
// The APU dispatcher manages the interface between the CV32E40P core and     //
// external coprocessors (FPU, custom accelerators, etc.). It handles:       //
//                                                                            //
// Key Responsibilities:                                                      //
// ---------------------                                                      //
// 1. Request Management: Track up to 2 outstanding coprocessor requests     //
// 2. Dependency Checking: Detect RAW/WAW hazards with pending operations    //
// 3. Stall Generation: Prevent pipeline corruption from resource conflicts  //
// 4. Response Routing: Direct returned results to correct destination       //
// 5. Latency Tracking: Handle single-cycle, dual-cycle, and multi-cycle ops //
//                                                                            //
// Request Pipeline:                                                          //
// -----------------                                                          //
// The dispatcher maintains up to 2 in-flight requests in a shallow queue:   //
// - Request (REQ): Current cycle's request (if enabled)                     //
// - Inflight: First queued request waiting for completion                   //
// - Waiting: Second queued request (if inflight is still active)            //
//                                                                            //
// Latency Classes:                                                           //
// ----------------                                                           //
// apu_lat encoding:                                                          //
//   00: Reserved / Invalid                                                   //
//   01: Single-cycle operation (result available immediately)               //
//   10: Two-cycle operation                                                  //
//   11: Multi-cycle operation (3+ cycles, variable latency)                 //
//                                                                            //
// Ordering Constraint:                                                       //
// -------------------                                                        //
// To prevent result reordering, the dispatcher enforces:                    //
// "New requests must have latency >= inflight operation latency"            //
//                                                                            //
// Example: If a 3-cycle op is inflight, cannot issue 1-cycle or 2-cycle    //
// ops until the 3-cycle op completes. This ensures results return in        //
// program order, simplifying writeback logic.                               //
//                                                                            //
// Alternative: Allow out-of-order completion with result buffer and tag     //
// tracking, but this adds significant complexity and area.                  //
//                                                                            //
// Stall Conditions:                                                          //
// -----------------                                                          //
// 1. FULL: Two requests already in-flight (no capacity)                     //
// 2. TYPE: Latency ordering constraint violated                             //
// 3. NACK: Coprocessor busy, cannot accept request this cycle              //
//                                                                            //
// Critical Paths:                                                            //
// ---------------                                                            //
// 1. Dependency check: 3x6-bit comparators + OR tree                        //
// 2. Stall logic: Latency comparison + valid signals                        //
// 3. Response mux: Select among req/inflight/waiting based on rvalid        //
//                                                                            //
// Alternative Implementation Suggestions:                                    //
// ---------------------------------------                                    //
// 1. Deeper queue: Support 4+ outstanding requests                          //
//    Benefit: Higher throughput for coprocessor-heavy code                  //
//    Cost: More area, complexity, deeper dependency checks                  //
//                                                                            //
// 2. Out-of-order completion: Add reorder buffer with tags                  //
//    Benefit: Better coprocessor utilization, no latency constraints        //
//    Cost: Significant area increase, CAM for tag matching                  //
//                                                                            //
// 3. Scoreboarding: Separate dependency tracker with per-register bits      //
//    Benefit: More precise dependency detection                             //
//    Cost: 32-bit scoreboard register + update logic                        //
//                                                                            //
// 4. Integrated FPU: Move FPU into main pipeline as EX2 stage              //
//    Benefit: Simpler interface, no dispatcher needed                       //
//    Cost: Increases main pipeline timing, harder to make FPU optional      //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40p_apu_disp (
    input logic clk_i,      // Clock signal
    input logic rst_ni,     // Active-low asynchronous reset

    // Request input from core pipeline
    input logic       enable_i,      // Enable APU request this cycle
    input logic [1:0] apu_lat_i,     // Latency class of current request (01/10/11)
    input logic [5:0] apu_waddr_i,   // Destination register address for current request

    // Response output to writeback stage
    output logic [5:0] apu_waddr_o,        // Register address of returning result
    output logic       apu_multicycle_o,   // Returning result is from multicycle op
    output logic       apu_singlecycle_o,  // No multi-cycle ops currently in-flight

    // Status signals
    output logic active_o,   // APU dispatcher has outstanding requests

    // Pipeline control
    output logic stall_o,    // Stall pipeline (cannot accept new request)

    // Dependency checking interface
    input  logic            is_decoding_i,        // Currently decoding an instruction
    input  logic [2:0][5:0] read_regs_i,          // Source registers of current instruction
    input  logic [2:0]      read_regs_valid_i,    // Valid bits for source registers
    output logic            read_dep_o,           // RAW dependency detected
    output logic            read_dep_for_jalr_o,  // Dependency for JALR (special handling)

    input  logic [1:0][5:0] write_regs_i,         // Destination registers to check
    input  logic [1:0]      write_regs_valid_i,   // Valid bits for dest registers
    output logic            write_dep_o,          // WAW dependency detected

    // Performance counter outputs
    output logic perf_type_o,  // Stalled due to latency type conflict
    output logic perf_cont_o,  // Stalled due to coprocessor NACK

    // APU interconnect interface (to coprocessor)
    // Handshake signals
    output logic apu_req_o,     // Request valid to coprocessor
    input  logic apu_gnt_i,     // Grant from coprocessor (request accepted)
    // Response channel
    input  logic apu_rvalid_i   // Response valid from coprocessor (result ready)

);

  ///////////////////////////////////////////////////////////////////////////////
  // Internal State Tracking
  ///////////////////////////////////////////////////////////////////////////////
  // Three instruction slots: REQ (current), INFLIGHT (queued), WAITING (queued)
  // Each slot tracks register address, validity, and completion status

  // Register addresses for each slot
  logic [5:0] addr_req, addr_inflight, addr_waiting;
  logic [5:0] addr_inflight_dn, addr_waiting_dn;
  
  // Validity flags - indicates slot contains an active request
  logic valid_req, valid_inflight, valid_waiting;
  logic valid_inflight_dn, valid_waiting_dn;
  
  // Return flags - indicates response received for this slot
  logic returned_req, returned_inflight, returned_waiting;

  logic       req_accepted;   // Current request was granted by coprocessor
  logic       active;         // At least one request is in-flight
  logic [1:0] apu_lat;        // Registered latency of inflight operation


  // Dependency tracking signals
  logic [2:0] read_deps_req, read_deps_inflight, read_deps_waiting;
  logic [1:0] write_deps_req, write_deps_inflight, write_deps_waiting;
  logic read_dep_req, read_dep_inflight, read_dep_waiting;
  logic write_dep_req, write_dep_inflight, write_dep_waiting;

  // Stall condition flags
  logic stall_full, stall_type, stall_nack;

  ///////////////////////////////////////////////////////////////////////////////
  // Request Generation and Acceptance Logic
  ///////////////////////////////////////////////////////////////////////////////
  
  // Generate request signal to coprocessor
  // Do not generate request if:
  // - stall_full: Queue is full (2 requests already inflight)
  // - stall_type: Latency ordering violation
  // Note: Still attempt request even if stall_nack (coprocessor busy),
  //       since grant status is unknown until tried
  assign valid_req         = enable_i & !(stall_full | stall_type);
  assign addr_req          = apu_waddr_i;

  // Request accepted when both core asserts valid and coprocessor grants
  assign req_accepted      = valid_req & apu_gnt_i;

  ///////////////////////////////////////////////////////////////////////////////
  // In-Flight Instruction Tracking
  ///////////////////////////////////////////////////////////////////////////////
  // Determine which slot (if any) received its response this cycle
  // Response (apu_rvalid_i) always corresponds to oldest outstanding request
  // due to in-order completion requirement
  
  // Response for current request (single-cycle operation)
  // Happens when: request this cycle, response this cycle, no queued requests
  assign returned_req      = valid_req & apu_rvalid_i & !valid_inflight & !valid_waiting;
  
  // Response for inflight slot (most common case)
  // Happens when: inflight valid, response arrives, no waiting request ahead
  assign returned_inflight = valid_inflight & (apu_rvalid_i) & !valid_waiting;
  
  // Response for waiting slot
  // Happens when: waiting valid, response arrives
  assign returned_waiting  = valid_waiting & (apu_rvalid_i);

  ///////////////////////////////////////////////////////////////////////////////
  // Sequential State Registers
  ///////////////////////////////////////////////////////////////////////////////
  // Register the inflight and waiting slot state
  // These form a 2-deep FIFO for tracking outstanding requests

  // Inflight and waiting registers
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      valid_inflight <= 1'b0;
      valid_waiting  <= 1'b0;
      addr_inflight  <= '0;
      addr_waiting   <= '0;
    end else begin
      valid_inflight <= valid_inflight_dn;
      valid_waiting  <= valid_waiting_dn;
      addr_inflight  <= addr_inflight_dn;
      addr_waiting   <= addr_waiting_dn;
    end
  end

  ///////////////////////////////////////////////////////////////////////////////
  // Inflight/Waiting Queue Management Logic
  ///////////////////////////////////////////////////////////////////////////////
  // Manages the 2-deep queue of outstanding requests
  // Handles: enqueueing new requests, retiring completed requests, shifting queue
  
  always_comb begin
    // Default: Hold current values
    valid_inflight_dn = valid_inflight;
    valid_waiting_dn  = valid_waiting;
    addr_inflight_dn  = addr_inflight;
    addr_waiting_dn   = addr_waiting;

    // Case 1: New multi-cycle request accepted (not returning immediately)
    if (req_accepted & !returned_req) begin
      // Move new request into inflight slot
      valid_inflight_dn = 1'b1;
      addr_inflight_dn  = addr_req;
      
      // If inflight slot already occupied (not retiring this cycle)
      if (valid_inflight & !(returned_inflight)) begin
        // Push current inflight into waiting slot
        valid_waiting_dn = 1'b1;
        addr_waiting_dn  = addr_inflight;
      end
      
      // Special case: waiting returns but inflight doesn't
      // Need to refill waiting with current inflight
      if (returned_waiting) begin
        valid_waiting_dn = 1'b1;
        addr_waiting_dn  = addr_inflight;
      end
    end 
    // Case 2: No new request, but inflight completes
    else if (returned_inflight) begin
      // Inflight done, shift waiting into inflight
      // (Handled by default logic - inflight cleared, waiting stays)
      valid_inflight_dn = '0;
      valid_waiting_dn  = '0;
      addr_inflight_dn  = '0;
      addr_waiting_dn   = '0;
    end 
    // Case 3: Waiting slot completes
    else if (returned_waiting) begin
      // Clear waiting slot
      valid_waiting_dn = '0;
      addr_waiting_dn  = '0;
    end
  end

  ///////////////////////////////////////////////////////////////////////////////
  // Active Status Tracking
  ///////////////////////////////////////////////////////////////////////////////
  // Dispatcher is active when there is at least one unreturned instruction
  // Used for: stall logic, dependency checks, performance counters
  assign active = valid_inflight | valid_waiting;

  ///////////////////////////////////////////////////////////////////////////////
  // Latency Type Register
  ///////////////////////////////////////////////////////////////////////////////
  // Store the latency type of the active operation
  // Used to enforce ordering constraint for subsequent requests
  // Only update when accepting a new request
  
  // Store the latency type whenever there is a request
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      apu_lat <= '0;
    end else begin
      if (valid_req) begin
        apu_lat <= apu_lat_i;  // Capture latency of new request
      end
    end
  end

  ///////////////////////////////////////////////////////////////////////////////
  // Dependency Checking Logic
  ///////////////////////////////////////////////////////////////////////////////
  // Detects register dependencies between new decode-stage instruction and
  // outstanding APU requests. Prevents RAW and WAW hazards.
  //
  // Check strategy: Compare each source/dest register against addresses in
  // all three slots (req, inflight, waiting)
  //
  // Alternative: Could use a 32-bit scoreboard with one bit per register
  // Benefit: O(1) lookup instead of O(n) comparisons
  // Cost: 32 bits + set/clear logic
  
  // Generate read dependency comparisons for each source register
  // There is a dependency if the register is equal to one of the instructions
  generate
    for (genvar i = 0; i < 3; i++) begin : gen_read_deps
      assign read_deps_req[i]      = (read_regs_i[i] == addr_req) & read_regs_valid_i[i];
      assign read_deps_inflight[i] = (read_regs_i[i] == addr_inflight) & read_regs_valid_i[i];
      assign read_deps_waiting[i]  = (read_regs_i[i] == addr_waiting) & read_regs_valid_i[i];
    end
  endgenerate

  // Generate write dependency comparisons for destination registers
  generate
    for (genvar i = 0; i < 2; i++) begin : gen_write_deps
      assign write_deps_req[i]      = (write_regs_i[i] == addr_req) & write_regs_valid_i[i];
      assign write_deps_inflight[i] = (write_regs_i[i] == addr_inflight) & write_regs_valid_i[i];
      assign write_deps_waiting[i]  = (write_regs_i[i] == addr_waiting) & write_regs_valid_i[i];
    end
  endgenerate

  // Reduce the individual dependency signals into one read and one write dependency per slot
  // Only consider unreturned instructions (returning this cycle doesn't count)
  assign read_dep_req = |read_deps_req & valid_req & !returned_req;
  assign read_dep_inflight = |read_deps_inflight & valid_inflight & !returned_inflight;
  assign read_dep_waiting = |read_deps_waiting & valid_waiting & !returned_waiting;
  assign write_dep_req = |write_deps_req & valid_req & !returned_req;
  assign write_dep_inflight = |write_deps_inflight & valid_inflight & !returned_inflight;
  assign write_dep_waiting = |write_deps_waiting & valid_waiting & !returned_waiting;

  // Final dependency outputs - combine all slots and gate with decode valid
  assign read_dep_o = (read_dep_req | read_dep_inflight | read_dep_waiting) & is_decoding_i;
  assign write_dep_o = (write_dep_req | write_dep_inflight | write_dep_waiting) & is_decoding_i;

  // Special JALR dependency: More conservative check
  // For JALR, check against enable (not just valid_req) to catch earlier
  assign read_dep_for_jalr_o = is_decoding_i & ((|read_deps_req & enable_i) |
                                                (|read_deps_inflight & valid_inflight) |
                                                (|read_deps_waiting & valid_waiting));

  ///////////////////////////////////////////////////////////////////////////////
  // Stall Signal Generation
  ///////////////////////////////////////////////////////////////////////////////
  // Three independent stall conditions (OR'd together for final stall)
  
  // Stall condition 1: Queue full
  // Both inflight and waiting slots are occupied - no room for new request
  assign stall_full = valid_inflight & valid_waiting;
  
  // Stall condition 2: Latency type conflict
  // To maintain in-order completion, new requests must have latency >= active latency
  // Stall if: (new_lat < active_lat) when dispatcher is active
  //
  // Detailed breakdown:
  // - apu_lat_i == 01 (1-cycle): Always conflicts if any operation active
  // - apu_lat_i == 10 (2-cycle): Conflicts if apu_lat == 11 (3-cycle active)
  // - apu_lat_i == 11 (3+cycle): Always conflicts (can't predict completion)
  //
  // Expression: stall if dispatcher active AND
  //   (requesting 1-cycle op) OR
  //   (requesting 2-cycle AND 3-cycle active) OR  
  //   (requesting multi-cycle - too unpredictable)
  assign stall_type      = enable_i  & active & ((apu_lat_i==2'h1) | ((apu_lat_i==2'h2) & (apu_lat==2'h3)) | (apu_lat_i==2'h3));
  
  // Stall condition 3: Coprocessor busy (NACK)
  // Request was attempted but coprocessor didn't grant
  // Need to retry next cycle
  assign stall_nack = valid_req & !apu_gnt_i;
  
  // Final stall output - OR of all stall conditions
  assign stall_o = stall_full | stall_type | stall_nack;

  ///////////////////////////////////////////////////////////////////////////////
  // APU Interface Outputs
  ///////////////////////////////////////////////////////////////////////////////
  
  // Request signal to coprocessor
  // Directly driven by valid_req (already accounts for stall_full/stall_type)
  assign apu_req_o = valid_req;


  // Determine write register address based on which slot returned this cycle
  // Priority: waiting > inflight > req (matches expected return order)
  always_comb begin
    apu_waddr_o = '0;
    if (returned_req) apu_waddr_o = addr_req;
    if (returned_inflight) apu_waddr_o = addr_inflight;
    if (returned_waiting) apu_waddr_o = addr_waiting;
  end

  // Output active signal (used by core pipeline control)
  assign active_o = active;

  // Performance counter signals
  assign perf_type_o = stall_type;  // Count cycles stalled due to latency conflict
  assign perf_cont_o = stall_nack;  // Count cycles stalled due to coprocessor busy

  // Operational mode indicators
  assign apu_multicycle_o = (apu_lat == 2'h3);  // Active operation is multi-cycle
  assign apu_singlecycle_o = ~(valid_inflight | valid_waiting);  // No queued operations

  ///////////////////////////////////////////////////////////////////////////////
  // Formal Verification Assertions
  ///////////////////////////////////////////////////////////////////////////////
  // Runtime checks to catch protocol violations

`ifdef CV32E40P_ASSERT_ON
  // Assertion: Response should only arrive when we have outstanding requests
  // Catches: Spurious responses from coprocessor
  assert property (@(posedge clk_i) (apu_rvalid_i) |-> (valid_req | valid_inflight | valid_waiting))
  else $warning("[APU Dispatcher] instruction returned while no instruction is in-flight");
  
  // Additional assertions that could enhance verification:
  //
  // 1. No response should arrive when dispatcher is idle (covered above)
  // 2. Stall signals should be mutually exclusive (they're not - can have multiple)
  // 3. Queue should never overflow (covered by stall_full logic)
  // 4. Dependency logic should never miss a true dependency
  // 5. Latency ordering should prevent younger ops from completing before older ops
`endif

endmodule
