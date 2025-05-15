// -----------------------------------------------------------------------------
// Module Name: regfile_stage
// Description: Implements a 32-register file for an RV32 processor.
//              Supports synchronous write operations and asynchronous read
//              operations. Interfaces with instruction and writeback
//              packets and outputs issue packets for the next pipeline stage.
// Author:      Bhanu Pande
// Date:        May 9, 2025
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

    // =========================================================================
    // Register File Declaration
    // =========================================================================
    // 32 registers, each 32 bits wide. Register x0 is always hardwired to zero.
    logic [31:0] regfile [0:31];

    // =========================================================================
    // Instruction Commit Signal
    // =========================================================================
    // Indicates whether the current instruction has been committed (written back)
    assign instruction_commit = writeback_packet.wb_enable;

    // =========================================================================
    // Synchronous Reset and Writeback Operation
    // =========================================================================
    // On reset, clear all registers. On writeback, update the destination register.
    always_ff @(posedge clk or negedge resetn) begin
        if (!resetn) begin
            // Reset all registers to 0 on an active-low reset
            for (int i = 0; i < 32; i++) begin
                regfile[i] <= 32'b0;
            end
        end else begin
            // Writeback operation: Write data to the register file if enabled
            // Register x0 (regfile[0]) is always zero and should not be written
            if (writeback_packet.valid_opcode && writeback_packet.wb_enable && (writeback_packet.wb_addr != 5'd0)) begin
                regfile[writeback_packet.wb_addr] <= writeback_packet.wb_data;
            end
        end
    end

    // =========================================================================
    // Asynchronous Read Operation
    // =========================================================================
    // Read rs1 and rs2 values from the register file for the next pipeline stage.
    always_comb begin
        // Read value of rs1; x0 is always zero
        issue_packet.rs1_value = (instruction_packet.rs1_sel == 5'd0) ? 32'b0 : regfile[instruction_packet.rs1_sel];
        // Read value of rs2; x0 is always zero
        issue_packet.rs2_value = (instruction_packet.rs2_sel == 5'd0) ? 32'b0 : regfile[instruction_packet.rs2_sel];

        // Pass the rs1 and rs2 selection signals to the issue packet
        issue_packet.rs1_sel = instruction_packet.rs1_sel;
        issue_packet.rs2_sel = instruction_packet.rs2_sel;

        // Set the destination register for writeback
        issue_packet.rd_sel = instruction_packet.rd_sel;

        // Pass immediate value and ALU operation code directly
        issue_packet.imm32 = instruction_packet.imm32;
        issue_packet.alu_op = instruction_packet.alu_op;

        // Pass the program counter (PC) to the next stage
        issue_packet.pc = instruction_packet.pc;

        // Pass the valid opcode and don't forward signals
        issue_packet.valid_opcode = instruction_packet.valid_opcode;
        issue_packet.dont_forward = instruction_packet.dont_forward;
    end

endmodule