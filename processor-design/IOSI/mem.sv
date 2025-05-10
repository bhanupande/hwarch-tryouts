module mem #(
    parameter N = 256,          // Depth of the memory
    parameter M = 32,           // Width of the data
    parameter LATENCY = 2       // Read latency
) (
    input logic clk,            // Clock signal
    input logic rstn,            // Reset signal
    input logic write_enable,   // Write enable signal
    input logic read_enable,    // Read enable signal
    input logic [$clog2(N)-1:0] write_addr, // Write address
    input logic [$clog2(N)-1:0] read_addr,  // Read address
    input logic [M-1:0] write_data,         // Data to write
    output logic [M-1:0] read_data          // Data read
);

    // Memory array
    logic [M-1:0] mem_array [0:N-1];

    // Write logic
    always_ff @(posedge clk) begin
        if (write_enable) begin
            mem_array[write_addr] <= write_data;
        end
    end

    // Read logic with latency
    assign read_data = read_enable ? mem_array[read_addr] : '0;

    // Latency simulation

endmodule