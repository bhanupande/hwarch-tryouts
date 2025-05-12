import rv32_pkg::*; // Import the package for constants and types
module mem_stage (
    input logic clk, // Clock signal
    input logic resetn, // Active low reset signal
    input rv32_ex2mem_wb_packet_t wb_in_packet, // Input write-back packet
    input rv32_ex_control_packet_t control_packet, // Input control packet
    input rv32_mem_packet_t mem_packet, // Input memory access packet
    output rv32_mem2wb_packet_t wb_out_packet // Output write-back packet
);
    logic [31:0] mem_read_data; // Output data from memory
    logic [31:0] load_data; // Output data from memory
    logic [31:0] mem_write_data; // Data to be written to memory
    logic mem_access; // Memory access signal

    assign mem_access = mem_packet.read_enable || mem_packet.write_enable; // Memory access signal

    assign wb_out_packet.wb_addr = wb_in_packet.wb_addr; // Register address to write back
    assign wb_out_packet.wb_data = mem_packet.read_enable ? load_data : wb_in_packet.wb_data; // Write back enable signal
    assign wb_out_packet.wb_enable = mem_packet.read_enable || wb_in_packet.wb_enable; // Write back enable signal

    always_comb begin
        case (control_packet.load_type)
            3'b000: load_data = {{24{mem_read_data[7]}}, mem_read_data[7:0]}; // Load data from memory
            3'b001: load_data = {{16{mem_read_data[15]}}, mem_read_data[15:0]}; // Load data from memory
            3'b010: load_data = mem_read_data; // Load data from memory
            3'b011: load_data = {24'h0, mem_read_data[7:0]}; // Load data from memory
            3'b100: load_data = {16'h0, mem_read_data[15:0]}; // Load data from memory
            default: load_data = '0; // Default case
        endcase
        case (control_packet.store_type)
            2'b00: mem_write_data = {{24{mem_packet.data[7]}}, mem_packet.data[7:0]}; // Store data to memory
            2'b01: mem_write_data = {{16{mem_packet.data[15]}}, mem_packet.data[15:0]}; // Store data to memory
            2'b10: mem_write_data = mem_packet.data; // Store data to memory
            default: mem_write_data = '0; // Default case
        endcase
    end

    mem dmem (
        .clk(clk),
        .rstn(resetn),
        .write_enable(mem_packet.write_enable), // No write operation in instruction fetch
        .read_enable(mem_packet.read_enable),  // Enable read operation
        .write_addr(mem_packet.addr),  // Not used
        .read_addr(mem_packet.addr), // Assuming word-aligned addresses
        .write_data(mem_write_data),  // Not used
        .read_data(mem_read_data) // Output instruction
    );


endmodule