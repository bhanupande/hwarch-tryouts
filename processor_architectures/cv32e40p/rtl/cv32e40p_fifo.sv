// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

// Copy of fifo_v3 from https://github.com/pulp-platform/common_cells b2a4b2d3decdfc152ad9b4564a48ed3b2649fd6c

////////////////////////////////////////////////////////////////////////////////
// Parameterized FIFO with Optional Fall-Through Mode
////////////////////////////////////////////////////////////////////////////////
//
// This module implements a synchronous FIFO (First-In-First-Out) queue with
// configurable depth, data width, and operating modes.
//
// Key Features:
// -------------
// 1. Parameterizable depth (0 to 2^32) and data width
// 2. Optional fall-through mode for zero-latency bypass
// 3. Flush capability (full or keep-first-entry)
// 4. Clock gating for power optimization
// 5. Full/empty status flags and occupancy counter
//
// Operating Modes:
// ----------------
// FALL_THROUGH = 0 (Normal Mode):
//   - Data written on cycle N is available for read on cycle N+1
//   - One cycle latency from push to first pop opportunity
//   - empty_o asserted when FIFO contains no data
//
// FALL_THROUGH = 1 (Fall-Through Mode):
//   - Data written to empty FIFO appears immediately on data_o
//   - Zero cycle latency for first entry
//   - Subsequent entries have normal 1-cycle latency
//   - empty_o considers both FIFO state and push_i signal
//
// Pointer Management:
// -------------------
// Uses circular buffer with read/write pointers:
// - write_pointer: Points to next write location
// - read_pointer: Points to next read location
// - Pointers wrap around at DEPTH boundary
// - status_cnt tracks occupancy (0 to DEPTH)
//
// Special Cases:
// --------------
// DEPTH = 0: Pass-through mode (combinational path from input to output)
//   - empty_o = ~push_i
//   - full_o = ~pop_i
//   - No storage, acts as wire with valid/ready handshake
//
// Flush Modes:
// ------------
// 1. flush_i: Complete flush, clear all entries
// 2. flush_but_first_i: Keep first entry, discard rest
//    Used for branch misprediction recovery in pipelines
//
// Clock Gating:
// -------------
// Memory updates are clock-gated when no write occurs
// Saves dynamic power during idle or read-only cycles
// gate_clock = 1 when no memory write needed
//
// Typical Usage in CV32E40P:
// --------------------------
// - Instruction prefetch buffer
// - Store buffer in LSU
// - Write-back buffer
//
// Critical Timing Paths:
// ----------------------
// 1. Push path: data_i -> mem_n -> mem_q (gated clock)
// 2. Pop path: mem_q[read_pointer_q] -> data_o (mux)
// 3. Pointer arithmetic: increment/wrap logic
// 4. Status counter: increment/decrement with simultaneous push/pop
//
// Alternative Implementations:
// ----------------------------
// 1. Shift Register FIFO: Data shifts through chain
//    Benefit: Simple, no pointers
//    Cost: High power (all stages toggle), poor for deep FIFOs
//
// 2. Dual-Port RAM FIFO: Use true dual-port memory
//    Benefit: Better for very deep FIFOs (>32 entries)
//    Cost: Requires dual-port RAM support
//
// 3. Gray Code Pointers: For async FIFO
//    Benefit: Safe clock domain crossing
//    Cost: More complex, not needed for synchronous design
//
// 4. Multi-Port FIFO: Multiple read/write ports
//    Benefit: Higher bandwidth
//    Cost: Complex arbitration, larger area
//
////////////////////////////////////////////////////////////////////////////////

module cv32e40p_fifo #(
    parameter bit FALL_THROUGH = 1'b0,     // Enable fall-through mode (0-cycle latency)
    parameter int unsigned DATA_WIDTH = 32,  // Width of data elements in bits
    parameter int unsigned DEPTH = 8,       // Number of entries (0 = passthrough)
    // DO NOT OVERWRITE THIS PARAMETER
    parameter int unsigned ADDR_DEPTH = (DEPTH > 1) ? $clog2(DEPTH) : 1  // Pointer width
) (
    input logic clk_i,    // Clock signal
    input logic rst_ni,   // Active-low asynchronous reset
    
    // Flush controls
    input logic flush_i,              // Flush entire FIFO (clear all)
    input logic flush_but_first_i,    // Flush except first entry (branch recovery)
    input logic testmode_i,           // Test mode to bypass clock gating
    
    // Status flags
    output logic full_o,              // FIFO full (cannot push)
    output logic empty_o,             // FIFO empty (cannot pop)
    output logic [ADDR_DEPTH:0] cnt_o,  // Current occupancy count (0 to DEPTH)
    
    // Push interface (write port)
    input logic [DATA_WIDTH-1:0] data_i,  // Data to write into FIFO
    input logic push_i,                   // Write enable (valid with ~full_o)
    
    // Pop interface (read port)
    output logic [DATA_WIDTH-1:0] data_o,  // Data read from FIFO
    input logic pop_i                      // Read enable (valid with ~empty_o)
);
  ///////////////////////////////////////////////////////////////////////////////
  // Local Parameters and Internal Signals
  ///////////////////////////////////////////////////////////////////////////////
  
  // FIFO depth - handle the case of pass-through, synthesizer will do constant propagation
  localparam int unsigned FIFO_DEPTH = (DEPTH > 0) ? DEPTH : 1;
  
  // Clock gating control signal
  // When high, memory write clock is gated to save power
  logic gate_clock;
  
  // Circular buffer pointers (current and next values)
  // These wrap around at FIFO_DEPTH boundary
  logic [ADDR_DEPTH - 1:0] read_pointer_n, read_pointer_q;
  logic [ADDR_DEPTH - 1:0] write_pointer_n, write_pointer_q;
  
  // Occupancy counter - tracks number of valid entries
  // Range: 0 to DEPTH (needs ADDR_DEPTH+1 bits)
  logic [ADDR_DEPTH:0] status_cnt_n, status_cnt_q;
  
  // FIFO storage memory (current and next values)
  logic [FIFO_DEPTH - 1:0][DATA_WIDTH-1:0] mem_n, mem_q;

  // Output occupancy count
  assign cnt_o = status_cnt_q;

  ///////////////////////////////////////////////////////////////////////////////
  // Status Flag Generation
  ///////////////////////////////////////////////////////////////////////////////
  // Derive full and empty flags from occupancy counter
  
  // Status flags
  generate
    if (DEPTH == 0) begin : gen_zero_depth
      // Special case: Zero-depth FIFO (pure passthrough/wire)
      // empty when not pushing, full when not popping
      assign empty_o = ~push_i;
      assign full_o  = ~pop_i;
    end else begin : gen_non_zero_depth
      // Normal case: Compare counter against depth
      // Full when all entries occupied
      assign full_o  = (status_cnt_q == FIFO_DEPTH[ADDR_DEPTH:0]);
      // Empty when no entries, unless fall-through with simultaneous push
      // In fall-through mode, pushing to empty FIFO makes data immediately available
      assign empty_o = (status_cnt_q == 0) & ~(FALL_THROUGH & push_i);
    end
  endgenerate

  ///////////////////////////////////////////////////////////////////////////////
  // Combinational Read/Write Logic
  ///////////////////////////////////////////////////////////////////////////////
  // Manages pointer updates, memory writes, and data output
  // Handles simultaneous push/pop operations correctly
  
  // read and write queue logic
  always_comb begin : read_write_comb
    // Default assignments - hold current state
    read_pointer_n  = read_pointer_q;
    write_pointer_n = write_pointer_q;
    status_cnt_n    = status_cnt_q;
    data_o          = (DEPTH == 0) ? data_i : mem_q[read_pointer_q];
    mem_n           = mem_q;
    gate_clock      = 1'b1;  // Gate clock by default (no write)

    //-------------------------------------------------------------------------
    // Push Operation: Write new data to FIFO
    //-------------------------------------------------------------------------
    if (push_i && ~full_o) begin
      // Write data to memory at current write pointer location
      mem_n[write_pointer_q] = data_i;
      
      // Un-gate the clock - we need to write to memory
      gate_clock = 1'b0;
      
      // Increment write pointer with wrap-around
      // When pointer reaches DEPTH-1, wrap back to 0
      if (write_pointer_q == FIFO_DEPTH[ADDR_DEPTH-1:0] - 1) write_pointer_n = '0;
      else write_pointer_n = write_pointer_q + 1;
      
      // Increment occupancy counter
      status_cnt_n = status_cnt_q + 1;
    end

    //-------------------------------------------------------------------------
    // Pop Operation: Read data from FIFO
    //-------------------------------------------------------------------------
    if (pop_i && ~empty_o) begin
      // Data output is default assignment (already muxed from mem_q)
      // Increment read pointer with wrap-around
      if (read_pointer_n == FIFO_DEPTH[ADDR_DEPTH-1:0] - 1) read_pointer_n = '0;
      else read_pointer_n = read_pointer_q + 1;
      
      // Decrement occupancy counter
      status_cnt_n = status_cnt_q - 1;
    end

    //-------------------------------------------------------------------------
    // Simultaneous Push and Pop
    //-------------------------------------------------------------------------
    // When pushing and popping simultaneously, counter stays the same
    // (One entry added, one removed - net zero change)
    if (push_i && pop_i && ~full_o && ~empty_o) status_cnt_n = status_cnt_q;

    //-------------------------------------------------------------------------
    // Fall-Through Mode: Zero-Latency Bypass
    //-------------------------------------------------------------------------
    // When FIFO is empty and data is pushed in fall-through mode,
    // data appears immediately on output without memory storage
    if (FALL_THROUGH && (status_cnt_q == 0) && push_i) begin
      data_o = data_i;  // Bypass directly to output
      if (pop_i) begin
        // Simultaneous push to empty FIFO and pop
        // Data passes through without modifying FIFO state
        status_cnt_n = status_cnt_q;
        read_pointer_n = read_pointer_q;
        write_pointer_n = write_pointer_q;
      end
    end
  end

  ///////////////////////////////////////////////////////////////////////////////
  // Sequential Logic: Pointer and Counter Registers
  ///////////////////////////////////////////////////////////////////////////////
  // Update pointers and counter on clock edge
  // Includes special flush modes for pipeline control
  
  // sequential process
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      // Reset: Initialize all pointers and counter to zero
      read_pointer_q  <= '0;
      write_pointer_q <= '0;
      status_cnt_q    <= '0;
    end else begin
      unique case (1'b1)
        //---------------------------------------------------------------------
        // Full Flush: Clear entire FIFO
        //---------------------------------------------------------------------
        // Used on branch misprediction or exception
        // All entries invalidated, pointers reset
        flush_i: begin
          read_pointer_q  <= '0;
          write_pointer_q <= '0;
          status_cnt_q    <= '0;
        end
        
        //---------------------------------------------------------------------
        // Conditional Flush: Keep first entry if present
        //---------------------------------------------------------------------
        // Used for speculative fetch: keep current instruction, discard rest
        // If FIFO has entries: keep entry at read_pointer, discard others
        // If FIFO empty: just clear to reset state
        flush_but_first_i: begin
          read_pointer_q  <= (status_cnt_q > 0) ? read_pointer_q : '0;
          write_pointer_q <= (status_cnt_q > 0) ? read_pointer_q + 1 : '0;
          status_cnt_q    <= (status_cnt_q > 0) ? 1'b1 : '0;
        end
        
        //---------------------------------------------------------------------
        // Normal Operation: Update from combinational logic
        //---------------------------------------------------------------------
        default: begin
          read_pointer_q  <= read_pointer_n;
          write_pointer_q <= write_pointer_n;
          status_cnt_q    <= status_cnt_n;
        end
      endcase
    end
  end

  ///////////////////////////////////////////////////////////////////////////////
  // Sequential Logic: Memory Storage with Clock Gating
  ///////////////////////////////////////////////////////////////////////////////
  // Memory updates only when gate_clock is low (write occurring)
  // Clock gating saves power during read-only or idle cycles
  
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      mem_q <= '0;  // Clear memory on reset
    end else if (!gate_clock) begin
      mem_q <= mem_n;  // Update memory only when writing
    end
    // else: Hold memory value (clock gated)
  end

  ///////////////////////////////////////////////////////////////////////////////
  // Assertions
  ///////////////////////////////////////////////////////////////////////////////
  // Formal verification checks for FIFO correctness

`ifdef CV32E40P_ASSERT_ON

  //-----------------------------------------------------------------------------
  // A0: DEPTH parameter validation
  //-----------------------------------------------------------------------------
  // FIFO must have at least one storage location
  // Zero-depth case is handled separately in status flag generation
  initial begin
    assert (DEPTH > 0)
    else $error("DEPTH must be greater than 0.");
  end

  //-----------------------------------------------------------------------------
  // A1: Push operation requires FIFO not full
  //-----------------------------------------------------------------------------
  // When FIFO is full, no push operations should occur
  // Violation indicates upstream logic error (missing full_o check)
  // Note: This checks full_o -> ~push_i (contrapositive of push_i -> ~full_o)
  full_write :
  assert property (@(posedge clk_i) disable iff (~rst_ni) (full_o |-> ~push_i))
  else $fatal(1, "Trying to push new data although the FIFO is full.");

  //-----------------------------------------------------------------------------
  // A2: Pop operation requires FIFO not empty
  //-----------------------------------------------------------------------------
  // When FIFO is empty, no pop operations should occur
  // Violation indicates downstream logic error (missing empty_o check)
  // Note: This checks empty_o -> ~pop_i (contrapositive of pop_i -> ~empty_o)
  empty_read :
  assert property (@(posedge clk_i) disable iff (~rst_ni) (empty_o |-> ~pop_i))
  else $fatal(1, "Trying to pop data although the FIFO is empty.");
`endif

  ///////////////////////////////////////////////////////////////////////////////
  // Implementation Notes
  ///////////////////////////////////////////////////////////////////////////////
  // ALTERNATIVE IMPLEMENTATION: Gray Code Pointers
  // For CDC (Clock Domain Crossing) FIFOs, use Gray-coded pointers:
  //   - Convert binary pointers to Gray code before crossing clock domains
  //   - Prevents metastability issues from multi-bit transitions
  //   - Requires 2-FF synchronizers on pointer signals
  //   - Example: pulp_platform_common_cells has cdc_fifo_gray.sv
  //
  // ALTERNATIVE IMPLEMENTATION: Registered Output
  // For better timing, add output register stage:
  //   - Breaks long combinational path from mem_q to data_o
  //   - Adds 1-cycle latency (not compatible with fall-through mode)
  //   - Improves Fmax for deep FIFOs (DEPTH > 8)
  //
  // POWER OPTIMIZATION: Enhanced Clock Gating
  // Additional gating opportunities:
  //   - Gate read_pointer when empty (no pops possible)
  //   - Gate write_pointer when full (no pushes possible)
  //   - Partition memory into banks, gate unused banks
  //   - Trade-off: More gating logic overhead vs power savings
  //
  // AREA OPTIMIZATION: Distributed RAM vs Registers
  // For FPGA implementations with DEPTH > 16:
  //   - Use distributed LUTRAM instead of flip-flops
  //   - Xilinx: Add (* ram_style = "distributed" *) attribute
  //   - Intel: Add ramstyle = "MLAB" attribute
  //   - Reduces slice/ALM usage significantly
  //
  // PERFORMANCE ENHANCEMENT: Bypass Path Prediction
  // For fall-through mode with high utilization:
  //   - Add predictor for fall-through vs buffered read
  //   - Pre-compute next output speculatively
  //   - Reduces critical path through empty check
  //   - Requires additional mux and prediction logic

endmodule  // cv32e40p_fifo
