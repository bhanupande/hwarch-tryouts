import rv32_pkg::*; // Import the package for constants and types
module memstage (
    input logic clk, // Clock signal
    input logic resetn, // Active low reset signal
    input logic reg_write_enable, // Register write enable signal
    input logic mem_read_enable, // Memory read enable signal
    input logic mem_write_enable, // Memory write enable signal
    input logic [2:0] load_sel, // Load select signal for memory operations
    input logic [1:0] store_sel, // Store select signal for memory operations
    input logic branch_taken, // Branch taken signal
    input logic [31:0] branch_target, // Branch target address
    input logic [2:0] branch_type, // Branch type signal
    input logic [31:0] mem_addr_from_ex, // Memory address for load/store operations
    input logic [31:0] mem_data_from_ex, // Data from EX stage for store operations
    input logic [4:0] reg_write_addr, // Register address to write back
    input logic [31:0] reg_write_data, // Data to write back to register file
    input logic [31:0] pc_from_ex, // Program Counter output
    input logic mem_ready, // Memory ready signal
    input logic [31:0] mem_data_in, // Data read from memory
    output logic [31:0] mem_data_out, // Data read from memory
    output logic mem_write_enable_out, // Memory write enable signal
    output logic mem_read_enable_out, // Memory read enable signal
    output logic [31:0] mem_addr_out, // Memory address for load/store operations 
    output logic [31:0] reg_write_data_out, // Data to write back to register file
    output logic reg_write_enable_out, // Register write enable signal
    output logic [4:0] reg_write_addr_out, // Register address to write back
    output logic [31:0] pc_next // Next program counter value
);

always_ff @(posedge clk or negedge resetn) begin
    if (!resetn) begin
        // Reset all outputs to default values
        mem_data_out <= 32'b0;
        mem_write_enable_out <= 1'b0;
        mem_read_enable_out <= 1'b0;
        mem_addr_out <= 32'b0;
        reg_write_data_out <= 32'b0;
        reg_write_enable_out <= 1'b0;
        reg_write_addr_out <= 5'b0;
        pc_next <= 32'b0;
    end else begin
        pc_next <= pc_from_ex; // Update the program counter
        // Memory stage logic
        if (mem_read_enable || mem_write_enable) begin
            // Memory operation is enabled
            mem_addr_out <= mem_addr_from_ex; // Set memory address for load/store operations
            if (mem_read_enable) begin
                // Memory read operation
                mem_read_enable_out <= 1'b1; // Enable memory read
                mem_write_enable_out <= 1'b0; // Disable memory write
                if (mem_ready) begin
                    // Memory is ready, read data
                    reg_write_data_out <= mem_data_in; // Data read from memory
                    reg_write_enable_out <= 1'b1; // Enable register write
                    reg_write_addr_out <= reg_write_addr; // Register address to write back
                end
            end
            else if (mem_write_enable & mem_ready) begin
                // Memory write operation
                mem_write_enable_out <= 1'b1; // Enable memory write
                mem_read_enable_out <= 1'b0; // Disable memory read
                reg_write_enable_out <= 1'b0; // Disable register write
                mem_data_out <= mem_data_from_ex; // Data to write to memory
            end
        end else begin
            // No memory operation, hold previous values
            mem_addr_out <= mem_addr_out;
            if (reg_write_enable) begin
                // Write back data to register file
                reg_write_data_out <= reg_write_data; // Data to write back
                reg_write_enable_out <= 1'b1; // Enable register write
                reg_write_addr_out <= reg_write_addr; // Register address to write back
            end else begin
                // No register write operation, hold previous values
                reg_write_data_out <= reg_write_data_out;
                reg_write_enable_out <= 1'b0;
                reg_write_addr_out <= reg_write_addr_out;
            end
        end
    end
end
endmodule