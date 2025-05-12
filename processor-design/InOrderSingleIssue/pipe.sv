import rv32_pkg::*; // Import the package containing the instruction packet structure
module pipe #(
    parameter type PTYPE = logic // Default to logic type
) (
    input PTYPE din_packet, // Input packet
    input logic clk,        // Clock signal
    input logic resetn,    // Active low reset signal
    input logic stall,  // Stall signal
    output PTYPE dout_packet // Output packet
);

always_ff @(posedge clk or negedge resetn) begin
    if (~resetn) begin
        dout_packet <= '0; // Reset output packet to zero
    end else if (~stall) begin
        dout_packet <= din_packet; // Pass input packet to output
    end
end

endmodule