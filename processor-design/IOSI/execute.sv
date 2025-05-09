//-----------------------------------------------------------------------------
// File: execute.sv
// Description: This module implements the execute stage of a RISC-V processor.
//              It performs ALU operations, memory access control, and branching.
// Author: [Your Name]
// Date: May 9, 2025
//-----------------------------------------------------------------------------

import rv32_pkg::*; // Import the package for constants and types

module execute (
    input logic clk, // Clock signal (used for pipelining if needed)
    input logic resetn, // Active low reset signal
    input logic alu_valid, // ALU valid signal
    input logic [31:0] pc_in, // Program Counter input
    input rv32_issue_packet_t issue_packet, // Decoded instruction packet
    output logic [31:0] alu_result, // ALU result output
    output logic reg_write_enable, // Register write enable signal
    output logic mem_read_enable, // Memory read enable signal
    output logic mem_write_enable, // Memory write enable signal
    output logic [31:0] pc_out // Program Counter output
);

    // Internal signals
    logic [31:0] rs1_value; // Source register 1 value
    logic [31:0] rs2_value; // Source register 2 value
    logic [31:0] rd_value; // Destination register value
    logic [31:0] imm32; // Immediate value
    logic [5:0] alu_op; // ALU operation code

    // Assign values from the issue packet
    assign rs1_value = issue_packet.rs1_value;
    assign rs2_value = issue_packet.rs2_value;
    assign rd_value = issue_packet.rd_value;
    assign imm32 = issue_packet.imm32;
    assign alu_op = issue_packet.alu_op;

    // ALU operation logic
    always_comb begin
        // Default values
        pc_out = pc_in + 4; // Default PC increment
        reg_write_enable = alu_valid; // Default to enabling register write
        mem_read_enable = 1'b0; // Default to no memory read
        mem_write_enable = 1'b0; // Default to no memory write

        // ALU operation based on the opcode
        case (alu_op)
            // M-type operations
            ALU_OP_NOP: alu_result = 32'b0; // No operation
            ALU_OP_MUL: alu_result = rs1_value * rs2_value; // Multiply
            ALU_OP_MULH: alu_result = $signed(rs1_value) * $signed(rs2_value); // Multiply high signed
            ALU_OP_MULHSU: alu_result = $signed(rs1_value) * $unsigned(rs2_value); // Multiply high signed/unsigned
            ALU_OP_MULHU: alu_result = $unsigned(rs1_value) * $unsigned(rs2_value); // Multiply high unsigned
            ALU_OP_DIV: alu_result = (rs2_value != 0) ? $signed(rs1_value) / $signed(rs2_value) : 32'b0; // Divide (handle div-by-zero)
            ALU_OP_DIVU: alu_result = (rs2_value != 0) ? $unsigned(rs1_value) / $unsigned(rs2_value) : 32'b0; // Divide unsigned
            ALU_OP_REM: alu_result = (rs2_value != 0) ? $signed(rs1_value) % $signed(rs2_value) : rs1_value; // Remainder
            ALU_OP_REMU: alu_result = (rs2_value != 0) ? $unsigned(rs1_value) % $unsigned(rs2_value) : rs1_value; // Remainder unsigned

            // R-type operations
            ALU_OP_ADD: alu_result = rs1_value + rs2_value;
            ALU_OP_SUB: alu_result = rs1_value - rs2_value;
            ALU_OP_SLL: alu_result = rs1_value << rs2_value[4:0]; // Limit shift amount to 5 bits
            ALU_OP_SLT: alu_result = ($signed(rs1_value) < $signed(rs2_value)) ? 1 : 0;
            ALU_OP_SLTU: alu_result = (rs1_value < rs2_value) ? 1 : 0;
            ALU_OP_XOR: alu_result = rs1_value ^ rs2_value;
            ALU_OP_SRL: alu_result = rs1_value >> rs2_value[4:0]; // Limit shift amount to 5 bits
            ALU_OP_SRA: alu_result = $signed(rs1_value) >>> rs2_value[4:0]; // Limit shift amount to 5 bits
            ALU_OP_OR: alu_result = rs1_value | rs2_value;
            ALU_OP_AND: alu_result = rs1_value & rs2_value;

            // Immediate operations
            ALU_OP_ADDI: alu_result = rs1_value + imm32;
            ALU_OP_SLTI: alu_result = ($signed(rs1_value) < $signed(imm32)) ? 1 : 0;
            ALU_OP_SLTIU: alu_result = (rs1_value < imm32) ? 1 : 0;
            ALU_OP_XORI: alu_result = rs1_value ^ imm32;
            ALU_OP_ORI: alu_result = rs1_value | imm32;
            ALU_OP_ANDI: alu_result = rs1_value & imm32;
            ALU_OP_SLLI: alu_result = rs1_value << imm32[4:0]; // Limit shift amount to 5 bits
            ALU_OP_SRLI: alu_result = rs1_value >> imm32[4:0]; // Limit shift amount to 5 bits
            ALU_OP_SRAI: alu_result = $signed(rs1_value) >>> imm32[4:0]; // Limit shift amount to 5 bits

            // Upper immediate operations
            ALU_OP_LUI: alu_result = {imm32[31:12], 12'b0}; // Load Upper Immediate
            ALU_OP_AUIPC: alu_result = pc_in + {imm32[31:12], 12'b0}; // Add Upper Immediate to PC

            // Load operations
            ALU_OP_LB, ALU_OP_LH, ALU_OP_LW, ALU_OP_LBU, ALU_OP_LHU, ALU_OP_LWU, ALU_OP_LD: begin
                alu_result = rs1_value + imm32; // Calculate memory address
                mem_read_enable = 1'b1; // Enable memory read
            end

            // Store operations
            ALU_OP_SB, ALU_OP_SH, ALU_OP_SW: begin
                alu_result = rs1_value + imm32; // Calculate memory address
                mem_write_enable = 1'b1; // Enable memory write
                reg_write_enable = 1'b0; // Disable register write
            end

            // Branch operations
            ALU_OP_BEQ: begin
                alu_result = (rs1_value == rs2_value) ? pc_in + imm32 : pc_in; // Branch if equal
                pc_out = alu_result; // Update PC output
                reg_write_enable = 1'b0; // Disable register write
            end
            ALU_OP_BNE: begin
                alu_result = (rs1_value != rs2_value) ? pc_in + imm32 : pc_in; // Branch if not equal
                pc_out = alu_result; // Update PC output
                reg_write_enable = 1'b0; // Disable register write
            end
            ALU_OP_BLT: begin
                alu_result = ($signed(rs1_value) < $signed(rs2_value)) ? pc_in + imm32 : pc_in; // Branch if less than
                pc_out = alu_result; // Update PC output
                reg_write_enable = 1'b0; // Disable register write
            end
            ALU_OP_BGE: begin
                alu_result = ($signed(rs1_value) >= $signed(rs2_value)) ? pc_in + imm32 : pc_in; // Branch if greater or equal
                pc_out = alu_result; // Update PC output
                reg_write_enable = 1'b0; // Disable register write
            end
            ALU_OP_BLTU: begin
                alu_result = (rs1_value < rs2_value) ? pc_in + imm32 : pc_in; // Branch if less than unsigned
                pc_out = alu_result; // Update PC output
                reg_write_enable = 1'b0; // Disable register write
            end
            ALU_OP_BGEU: begin
                alu_result = (rs1_value >= rs2_value) ? pc_in + imm32 : pc_in; // Branch if greater or equal unsigned
                pc_out = alu_result; // Update PC output
                reg_write_enable = 1'b0; // Disable register write
            end

            // Jump operations
            ALU_OP_JAL: begin
                alu_result = pc_in + 4; // Jump and Link
                pc_out = pc_in + imm32; // Update PC output
            end
            ALU_OP_JALR: begin
                alu_result = (rs1_value + imm32) & 32'hFFFFFFFE; // Jump and Link Register
                pc_out = alu_result; // Update PC output
            end

            // Default case
            default: alu_result = 32'b0; // Default to zero
        endcase
    end
endmodule