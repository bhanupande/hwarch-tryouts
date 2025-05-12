import rv32_pkg::*; // Import the package containing the instruction packet structure
module if_stage (
    input logic clk,
    input logic resetn,
    input rv32_branch_packet_t branch_packet,
    input logic stall_fetch,
    output rv32_if_packet_t if_packet_out
);
    logic imem_read_enable;
    // PC register
    always @(posedge clk or negedge resetn) begin
        if (~resetn) begin
            if_packet_out.pc <= 32'b0; // Reset PC to 0
            imem_read_enable <= 1'b0; // Disable instruction memory read
        end else if (~stall_fetch && branch_packet.branch_taken) begin
            if_packet_out.pc <= branch_packet.branch_target; // Update PC to branch target
            imem_read_enable <= 1'b1; // Enable instruction memory read
        end else if (~stall_fetch && imem_read_enable) begin
            if_packet_out.pc <= if_packet_out.pc + 4; // Increment PC by 4 for next instruction
            imem_read_enable <= 1'b1; // Enable instruction memory read
        end else if (~stall_fetch) begin
            imem_read_enable <= 1'b1; // Enable instruction memory read
        end else begin
            imem_read_enable <= 1'b0; // Disable instruction memory read during stall
        end
    end

    mem imem (
        .clk(clk),
        .rstn(resetn),
        .write_enable(1'b0), // No write operation in instruction fetch
        .read_enable(imem_read_enable),  // Enable read operation
        .write_addr(32'b0),  // Not used
        .read_addr(if_packet_out.pc[31:2]), // Assuming word-aligned addresses
        .write_data(32'b0),  // Not used
        .read_data(if_packet_out.instruction) // Output instruction
    );

endmodule