// -----------------------------------------------------------------------------
// Module: mem
// Description: Parameterized memory module with configurable depth, width, and
//              read latency. Supports synchronous read and write operations.
// Parameters:
//   - N: Depth of the memory (number of entries).
//   - M: Width of each memory entry (in bits).
//   - LATENCY: Read latency (not fully implemented in this version).
// Author: Bhanu Pande
// Date: May 12, 2025
// -----------------------------------------------------------------------------

module mem #(
    parameter N = 1024,          // Depth of the memory
    parameter M = 32,            // Width of the data
    parameter LATENCY = 2        // Read latency (not implemented)
) (
    input  logic clk,            // Clock signal
    input  logic rstn,           // Active-low reset signal
    input  logic write_enable,   // Write enable signal
    input  logic read_enable,    // Read enable signal
    input  logic [$clog2(N)-1:0] write_addr, // Write address
    input  logic [$clog2(N)-1:0] read_addr,  // Read address
    input  logic [M-1:0] write_data,         // Data to write
    output logic [M-1:0] read_data           // Data read
);

    // Memory array declaration
    logic [M-1:0] mem_array [0:N-1]; // Memory storage

    // Write logic: Write data to memory on a positive clock edge if enabled
    always_ff @(posedge clk) begin
        if (write_enable) begin
            mem_array[write_addr] <= write_data;
        end
    end

    // Read logic: Output data from memory if read is enabled
    assign read_data = read_enable ? mem_array[read_addr] : '0;

    // Note: LATENCY parameter is defined but not implemented in this version.
    //       Future versions can include pipelining or delay logic to simulate latency.

endmodule