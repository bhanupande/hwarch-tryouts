// -----------------------------------------------------------------------------
// Module:      mem
// Description: Parameterized memory module with configurable depth, width, and
//              read latency. Supports synchronous write and combinational read.
//              Used for both instruction and data memory in the processor.
// Parameters:
//   - N:       Depth of the memory (number of entries).
//   - M:       Width of each memory entry (in bits).
//   - LATENCY: Read latency (not implemented in this version).
// Author:      Bhanu Pande
// Date:        May 12, 2025
// -----------------------------------------------------------------------------

module mem #(
    parameter N = 1024,          // Depth of the memory (number of words)
    parameter M = 32,            // Width of each memory word (bits)
    parameter LATENCY = 2        // Read latency (not implemented)
) (
    input  logic clk,            // Clock signal
    input  logic rstn,           // Active-low reset signal
    input  logic write_enable,   // Write enable signal (synchronous)
    input  logic read_enable,    // Read enable signal (combinational)
    input  logic [$clog2(N)-1:0] write_addr, // Write address
    input  logic [$clog2(N)-1:0] read_addr,  // Read address
    input  logic [M-1:0] write_data,         // Data to write
    output logic [M-1:0] read_data           // Data read from memory
);

    // =========================================================================
    // Memory Array Declaration
    // =========================================================================
    // Implements the actual storage for the memory.
    logic [M-1:0] mem_array [0:N-1]; // Memory storage array

    // =========================================================================
    // Synchronous Write Logic
    // =========================================================================
    // On the rising edge of the clock, write data to memory if write_enable is asserted.
    always_ff @(posedge clk) begin
        if (write_enable) begin
            mem_array[write_addr] <= write_data;
        end
    end

    // =========================================================================
    // Combinational Read Logic
    // =========================================================================
    // Output data from memory at the given read address if read_enable is asserted.
    // Otherwise, output zeros.
    assign read_data = read_enable ? mem_array[read_addr] : '0;

    // =========================================================================
    // Note on Read Latency
    // =========================================================================
    // The LATENCY parameter is defined for future use but is not implemented in this version.
    // To simulate memory latency, pipelining or delay logic can be added in future revisions.

endmodule