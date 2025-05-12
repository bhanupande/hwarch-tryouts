// -----------------------------------------------------------------------------
// Module: if_stage
// Description: Instruction Fetch (IF) stage for an in-order single-issue processor.
//              This module handles the program counter (PC) updates and instruction
//              memory read operations. It supports branch handling and fetch stalling.
// Author: Bhanu Pande
// Date: May 12, 2025
// ----------------------------------------------------------------------------

import rv32_pkg::*; // Import the package containing the instruction packet structure

module if_stage (
    input  logic clk,                       // Clock signal
    input  logic resetn,                    // Active-low reset signal
    input  rv32_branch_packet_t branch_packet, // Branch packet containing branch info
    input  logic stall_fetch,               // Stall signal for fetch stage
    output rv32_if_packet_t if_packet_out   // Output packet containing PC and instruction
);

    // Internal signal to enable instruction memory read
    logic imem_read_enable;

    // PC register and control logic
    always @(posedge clk or negedge resetn) begin
        if (~resetn) begin
            // Reset PC and disable instruction memory read
            if_packet_out.pc <= 32'b0;
            imem_read_enable <= 1'b0;
        end else if (~stall_fetch && branch_packet.branch_taken) begin
            // Branch taken: Update PC to branch target and enable memory read
            if_packet_out.pc <= branch_packet.branch_target;
            imem_read_enable <= 1'b1;
        end else if (~stall_fetch && imem_read_enable) begin
            // Normal operation: Increment PC by 4 and enable memory read
            if_packet_out.pc <= if_packet_out.pc + 4;
            imem_read_enable <= 1'b1;
        end else if (~stall_fetch) begin
            // No branch or stall: Enable memory read
            imem_read_enable <= 1'b1;
        end else begin
            // Stall: Disable memory read
            imem_read_enable <= 1'b0;
        end
    end

    // Instruction memory interface
    mem imem (
        .clk(clk),
        .rstn(resetn),
        .write_enable(1'b0),                  // No write operation in instruction fetch
        .read_enable(imem_read_enable),      // Enable read operation
        .write_addr(32'b0),                  // Not used
        .read_addr(if_packet_out.pc[31:2]),  // Word-aligned read address
        .write_data(32'b0),                  // Not used
        .read_data(if_packet_out.instruction) // Output instruction
    );

endmodule