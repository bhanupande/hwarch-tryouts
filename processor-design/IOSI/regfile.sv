// -----------------------------------------------------------------------------
// Module Name: regfile
// Description: This module implements a 32-register file for an RV32 processor.
//              It supports synchronous write operations and asynchronous read
//              operations. The module interfaces with instruction and writeback
//              packets and outputs issue packets for the next pipeline stage.
// Author: Bhanu Pande
// Date: May 9, 2025
// ----------------------------------------------------------------------------

import rv32_pkg::*; // Import the package for constants and types

module regfile (
    input logic clk, // Clock signal
    input logic resetn, // Active low reset signal
    input rv32_instr_packet_t instruction_packet, // Instruction packet containing rs1, rs2, rd, imm, alu_op
    input rv32_writeback_packet_t writeback_packet, // Writeback packet containing wb_reg and wb_data
    output rv32_issue_packet_t issue_packet // Output packet for the next stage
);

    // Declare registers for the register file
    logic [31:0] regfile [0:31]; // 32 registers, each 32 bits wide

    // Synchronous reset and writeback operation
    always_ff @(posedge clk or negedge resetn) begin
        if (!resetn) begin
            // Reset all registers to 0
            for (int i = 0; i < 32; i++) begin
                regfile[i] <= 32'b0;
            end
        end else begin
            // Writeback operation
            if (writeback_packet.wb_en) begin
                regfile[writeback_packet.wb_sel] <= writeback_packet.wb_data;
            end
        end
    end

    // Asynchronous read operation
    always_comb begin
        // Read rs1 and rs2 values from the register file
        issue_packet.rs1_value = regfile[instruction_packet.rs1_sel];
        issue_packet.rs2_value = regfile[instruction_packet.rs2_sel];
        // Pass immediate value and ALU operation code directly
        issue_packet.imm32 = instruction_packet.imm32;
        issue_packet.alu_op = instruction_packet.alu_op;
    end

endmodule