// -----------------------------------------------------------------------------
// Module: pipe
// Description: Generic pipeline register module for passing data between stages
//              in an in-order single-issue processor. Supports stalling and reset.
// Parameters:
//   - PTYPE: Data type of the input and output packets (default: logic).
// Author: Bhanu Pande
// Date: May 12, 2025
// ----------------------------------------------------------------------------

import rv32_pkg::*; // Import the package containing the instruction packet structure

module pipe #(
    parameter type PTYPE = logic // Default to logic type
) (
    input  PTYPE din_packet,  // Input packet
    input  logic clk,         // Clock signal
    input  logic resetn,      // Active-low reset signal
    input  logic stall,       // Stall signal
    input  logic flush,      // Flush signal
    output PTYPE dout_packet  // Output packet
);

    // Sequential logic for pipeline register
    always_ff @(posedge clk or negedge resetn) begin
        if (~resetn) begin
            // On reset, clear the output packet to zero
            dout_packet <= '0;
        end else if (flush) begin
            // On flush, clear the output packet to zero
            dout_packet <= '0;
        end else if (~stall) begin
            // On normal operation (not stalled), transfer input to output
            dout_packet <= din_packet;
        end
        // If stalled, retain the previous value of dout_packet (no assignment)
    end

endmodule