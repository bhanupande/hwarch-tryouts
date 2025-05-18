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

module mem_ctrl #(
    parameter DEPTH = 1024,          // Depth of the memory (number of words)
    parameter WIDTH = 32,            // Width of each memory word (bits)
    parameter LATENCY = 0        // Read latency (not implemented)
) (
    input  logic clk,            // Clock signal
    input  logic rstn,           // Active-low reset signal
    input  logic write_enable,   // Write enable signal (synchronous)
    input  logic read_enable,    // Read enable signal (combinational)
    input  logic [$clog2(DEPTH)-1:0] write_addr, // Write address
    input  logic [$clog2(DEPTH)-1:0] read_addr,  // Read address
    input  logic [WIDTH-1:0] write_data,         // Data to write
    output logic mem_ready,      // Memory ready signal (always high)
    output logic [WIDTH-1:0] read_data           // Data read from memory
);
    localparam REGOUT = LATENCY>0 ? 1 : 0; // Register output based on latency
    mem_model #(
        .Mode("SRAM"),             // Memory mode (SRAM)
        .AW($clog2(DEPTH)),        // Address width
        .DW(WIDTH),                // Data width
        .REGOUT(REGOUT),           // Register output (1: registered)
        .LATENCY(LATENCY),         // Read latency (not implemented)
        .DEPTH(DEPTH)              // Depth of the memory
    ) mem_inst (
        .cs(read_enable || write_enable),             // Chip select (always active)
        .wren(write_enable),   // Write enable
        .rden(read_enable),    // Read enable
        .memclk(clk),          // Memory clock
        .din(write_data),      // Data input
        .memwaddr(write_addr),  // Memory address for write
        .memraddr(read_addr),  // Memory address for read
        .dout(read_data)       // Data output (read data)
    );
    logic read_enable_reg; // Register to hold read enable state
    // =========================================================================
    // Note on Read Latency
    // =========================================================================
    // The LATENCY parameter is defined for future use but is not implemented in this version.
    // To simulate memory latency, pipelining or delay logic can be added in future revisions.
    generate if (LATENCY > 0) begin
        // Pipelining logic can be added here for read latency
        // For now, we will keep it simple and not implement any latency
        always_ff @(posedge clk or negedge rstn) begin
            if (~rstn)  read_enable_reg <= 1'b0; // Reset read enable register
            else        read_enable_reg <= read_enable; // Update read enable register
        end
        assign mem_ready = ~read_enable || read_enable_reg; // Memory ready signal
    end else begin
        assign mem_ready = 1'b1; // Always ready if no latency
    end
    endgenerate
endmodule