// ============================================================================
//  Module:      mem_model
//  Description: Simple synchronous SRAM model with separate read and write
//               enables. Parameterizable address width, data width, and depth.
//  Author:      Bhanu Pande
//  Date:        05/17/2025
//  Project:     InOrderSingleIssue Processor Primitives
// ============================================================================

module mem_model #(
    // Modes
    parameter Mode = "SRAM", // Memory mode (SRAM, CAM)
    // Address width (number of address bits)
    parameter int AW   = 8,
    // Data width (number of bits per word)
    parameter int DW   = 8,
    // Depth (number of words)
    parameter int DEPTH  = 8,
    parameter int REGOUT = 1 // Register output (0: combinational, 1: registered)
)
(
    input logic cs,                  // Chip select
    input logic wren,                // Write enable (active high)
    input logic rden,                // Read enable (active high)
    input logic memclk,              // Memory clock
    input logic [DW-1:0]  din,       // Data input
    input logic [AW-1:0]  memwaddr,   // Memory write address
    input logic [AW-1:0]  memraddr,   // Memory read address
    output logic match,     // Match signal for CAM
    output logic [AW-1:0] index,     // Index for CAM
    output logic [DW-1:0]  dout      // Data output
);

// Internal memory array
logic [DW-1:0] mem_ram [DEPTH-1:0];

generate
if (Mode == "CAM") begin
    // Content Addressable Memory (CAM) specific logic can be added here
    // For now, we will treat it as a simple SRAM for demonstration purposes
    always_comb begin
        index = '0; // Default index
        dout = '0;  // Default output
        match = 1'b0; // Default match signal
        if (cs == 1'b1) begin
            // CAM specific logic (e.g., match search)
            for (int i=0; i<DEPTH; i++) begin
                if (mem_ram[i] == din) begin
                    dout = mem_ram[i];
                    index = i;
                    match = 1'b1; // Match found
                end
            end
        end
    end
end
else if (Mode == "SRAM") begin
    // Synchronous read/write logic
    always @ (posedge memclk) begin
        if (cs == 1'b1) begin
            // Write operation (write enable high, read enable low)
            if (wren == 1'b1 && rden == 1'b0) begin
                mem_ram[memwaddr] <= din;
            end
        end
    end
    if (REGOUT) begin
        // Registered output logic
        always @ (posedge memclk) begin
            if (cs == 1'b1 && rden == 1'b1) begin
                dout <= mem_ram[memraddr];
            end
        end
    end else begin
        // Combinational output logic
        always_comb begin
            if (cs == 1'b1 && rden == 1'b1) begin
                dout = mem_ram[memraddr];
            end else begin
                dout = '0; // Default output when not selected or not reading
            end
        end
    end
end
endgenerate
endmodule