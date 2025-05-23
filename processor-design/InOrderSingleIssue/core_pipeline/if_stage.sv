// -----------------------------------------------------------------------------
// Module:      if_stage
// Description: Instruction Fetch (IF) stage for an in-order single-issue processor.
//              Handles program counter (PC) updates, instruction memory reads,
//              branch redirection, and fetch stalling.
// Author:      Bhanu Pande
// Date:        May 12, 2025
// ----------------------------------------------------------------------------

import rv32_pkg::*; // Import the package containing the instruction packet structure

module if_stage (
    input  logic clk,                        // Clock signal
    input  logic resetn,                     // Active-low reset signal
    input  rv32_branch_packet_t branch_packet, // Branch packet containing branch info
    input  logic stall_fetch,                // Stall signal for fetch stage
    output rv32_if_packet_t if_packet_out    // Output packet containing PC and instruction
);

    // Internal signal to enable instruction memory read
    logic imem_read_enable;
    logic [31:0] pc_next; // Next PC value for instruction fetch

    // =========================================================================
    // PC Register and Control Logic
    // =========================================================================
    // Handles PC updates for normal execution, branch redirection, and stalling.
    always_ff @(posedge clk or negedge resetn) begin
        if (~resetn) begin
            // On reset: set PC to 0 and disable instruction memory read
            pc_next <= 32'b0;
            imem_read_enable <= 1'b0;
        end else if (branch_packet.branch_taken) begin
            // On branch taken: update PC to branch target and enable memory read
            pc_next <= branch_packet.branch_target;
            imem_read_enable <= 1'b1;
        end else if (~stall_fetch && imem_read_enable) begin
            // Normal operation: increment PC by 4 (next instruction) and enable memory read
            pc_next <= pc_next + 4;
            imem_read_enable <= 1'b1;
        end else if (~stall_fetch) begin
            // No branch, no stall: enable memory read (PC remains unchanged)
            imem_read_enable <= 1'b1;
        end else begin
            // On stall: disable memory read (PC remains unchanged)
            imem_read_enable <= 1'b0;
        end
    end

    // PC output register logic
    always_ff @(posedge clk or negedge resetn) begin
        if (~resetn)
            if_packet_out.pc <= 32'b0;      // On reset, set output PC to 0
        else
            if_packet_out.pc <= pc_next;    // Otherwise, update output PC to next value
    end

    // =========================================================================
    // Instruction Memory Interface
    // =========================================================================
    // Instantiates the instruction memory controller and connects the PC for instruction fetch.
    // Only read operations are performed in the IF stage.
    mem_ctrl imem (
        .clk(clk),
        .rstn(resetn),
        .write_enable(1'b0),                   // No write operation in instruction fetch
        .read_enable(imem_read_enable),        // Enable read operation
        .write_addr(32'b0),                    // Not used
        .read_addr(pc_next[31:2]),             // Word-aligned read address
        .write_data(32'b0),                    // Not used
        .mem_ready(if_packet_out.mem_ready),   // Memory ready signal
        .read_data(if_packet_out.instruction)  // Output instruction
    );

endmodule