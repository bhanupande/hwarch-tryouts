// -----------------------------------------------------------------------------
// Module Name: regfile_stage
// Description: This module implements a 32-register file for an RV32 processor.
//              It supports synchronous write operations and asynchronous read
//              operations. The module interfaces with instruction and writeback
//              packets and outputs issue packets for the next pipeline stage.
// Author: Bhanu Pande
// Date: May 9, 2025
// ----------------------------------------------------------------------------

import rv32_pkg::*; // Import the package for constants and types

module regfile_stage (
    input logic clk,                          // Clock signal
    input logic resetn,                       // Active-low reset signal
    input rv32_instr_packet_t instruction_packet, // Instruction packet containing rs1, rs2, rd, imm, alu_op
    input rv32_mem2wb_packet_t writeback_packet,  // Writeback packet containing wb_reg and wb_data
    output rv32_issue_packet_t issue_packet,      // Output packet for the next stage
    output logic instruction_commit              // Signal indicating instruction commit
);

    // Declare registers for the register file
    logic [31:0] regfile [0:31]; // 32 registers, each 32 bits wide

    // Instruction Commit
    // This signal indicates whether the current instruction has been committed
    assign instruction_commit = writeback_packet.wb_enable;

    // Synchronous reset and writeback operation
    always_ff @(posedge clk or negedge resetn) begin
        if (!resetn) begin
            // Reset all registers to 0 on an active-low reset
            for (int i = 0; i < 32; i++) begin
                regfile[i] <= 32'b0; // Clear each register
            end
        end else begin
            // Writeback operation: Write data to the register file if enabled
            if (writeback_packet.valid_opcode && writeback_packet.wb_enable) begin
                regfile[writeback_packet.wb_addr] <= writeback_packet.wb_data; // Write data to the specified register
            end
        end
    end

    // Asynchronous read operation
    always_comb begin
        // Read rs1 and rs2 values from the register file
        // These values are used as inputs for the ALU or other processing stages
        issue_packet.rs1_value = regfile[instruction_packet.rs1_sel]; // Read value of rs1
        issue_packet.rs2_value = regfile[instruction_packet.rs2_sel]; // Read value of rs2

        // Pass the rs1 and rs2 selection signals to the issue packet
        // These signals indicate which registers were read
        issue_packet.rs1_sel = instruction_packet.rs1_sel; // Forward rs1 selection
        issue_packet.rs2_sel = instruction_packet.rs2_sel; // Forward rs2 selection

        // Set the destination register for writeback
        // This is the register where the result of the instruction will be written
        issue_packet.rd_sel = instruction_packet.rd_sel; // Forward destination register selection

        // Pass immediate value and ALU operation code directly
        // These are used for immediate-based instructions and ALU operations
        issue_packet.imm32 = instruction_packet.imm32; // Forward immediate value
        issue_packet.alu_op = instruction_packet.alu_op; // Forward ALU operation code

        // Pass the program counter (PC) to the next stage
        // This is used for debugging or branch/jump instructions
        issue_packet.pc = instruction_packet.pc; // Forward program counter

        // Pass the valid opcode signal to indicate if the instruction is valid
        issue_packet.valid_opcode = instruction_packet.valid_opcode; // Forward valid opcode signal
    end

endmodule