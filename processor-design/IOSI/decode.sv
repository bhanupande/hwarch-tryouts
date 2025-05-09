// *****************************************************************************************
// File: decode.sv
// Description: This module implements the decode stage of a RISC-V processor. It decodes
//              the 32-bit instruction into control signals and instruction packet fields
//              such as source registers, destination register, and immediate values.
// Author: Bhanu Pande
// Date: May 9, 2025
// *****************************************************************************************

`include "rv32_pkg.sv" // Include package for constants and types

// *****************************************************************************************
// Module: decode
// Inputs:
//   - instruction: 32-bit RISC-V instruction to be decoded
// Outputs:
//   - instruction_packet: Struct containing decoded instruction fields (rs1, rs2, rd, imm, alu_op)
// *****************************************************************************************
module decode (
    input logic [31:0] instruction,       // 32-bit RISC-V instruction
    output rv32_instr_packet_t instruction_packet // Decoded instruction packet
);

    // Extract opcode, funct3, and funct7 fields from the instruction
    rv32_opcode_t opcode = instruction[6:0];       // Opcode field (bits 6:0)
    rv32_funct3_t funct3 = instruction[14:12];     // Funct3 field (bits 14:12)
    rv32_funct7_t funct7 = instruction[31:25];     // Funct7 field (bits 31:25)

    // Combinational logic for decoding the instruction
    always_comb begin
        // Initialize outputs to default values
        instruction_packet = '{rs1_value: 5'b0, rs2_value: 5'b0, rd_value: 5'b0, imm32: 32'b0, alu_op: ALU_OP_NOP};

        // Decode based on opcode
        case (opcode)
            RV32I_LUI: begin
                // Load Upper Immediate
                instruction_packet.rd_value = instruction[11:7]; // Destination register
                instruction_packet.imm32 = {instruction[31:12], 12'b0}; // Immediate value
                instruction_packet.alu_op = ALU_OP_LUI; // ALU operation
            end
            RV32I_AUIPC: begin
                // Add Upper Immediate to PC
                instruction_packet.rd_value = instruction[11:7];
                instruction_packet.imm32 = {instruction[31:12], 12'b0};
                instruction_packet.alu_op = ALU_OP_AUIPC;
            end
            RV32I_JAL: begin
                // Jump and Link
                instruction_packet.rd_value = instruction[11:7];
                instruction_packet.imm32 = {{11{instruction[31]}}, instruction[19:12], instruction[20], instruction[30:21], 1'b0};
                instruction_packet.alu_op = ALU_OP_JAL;
            end
            RV32I_JALR: begin
                // Jump and Link Register
                instruction_packet.rs1_value = instruction[19:15];
                instruction_packet.rd_value = instruction[11:7];
                instruction_packet.imm32 = {{20{instruction[31]}}, instruction[30:20]};
                instruction_packet.alu_op = ALU_OP_JALR;
            end
            RV32I_BRANCH: begin
                // Branch instructions
                instruction_packet.rs1_value = instruction[19:15];
                instruction_packet.rs2_value = instruction[24:20];
                instruction_packet.imm32 = {{20{instruction[31]}}, instruction[7], instruction[30:25], instruction[11:8], 1'b0};
                case (funct3)
                    RV32I_F3_BEQ: instruction_packet.alu_op = ALU_OP_BEQ; // Branch if Equal
                    RV32I_F3_BNE: instruction_packet.alu_op = ALU_OP_BNE; // Branch if Not Equal
                    RV32I_F3_BLT: instruction_packet.alu_op = ALU_OP_BLT; // Branch if Less Than
                    RV32I_F3_BGE: instruction_packet.alu_op = ALU_OP_BGE; // Branch if Greater or Equal
                    RV32I_F3_BLTU: instruction_packet.alu_op = ALU_OP_BLTU; // Branch if Less Than Unsigned
                    RV32I_F3_BGEU: instruction_packet.alu_op = ALU_OP_BGEU; // Branch if Greater or Equal Unsigned
                    default: instruction_packet.alu_op = ALU_OP_NOP; // Default to no operation
                endcase
            end
            RV32I_LOAD: begin
                // Load instructions
                instruction_packet.rs1_value = instruction[19:15];
                instruction_packet.rd_value = instruction[11:7];
                instruction_packet.imm32 = {{20{instruction[31]}}, instruction[31:20]};
                case (funct3)
                    RV32I_F3_LB: instruction_packet.alu_op = ALU_OP_LB; // Load Byte
                    RV32I_F3_LH: instruction_packet.alu_op = ALU_OP_LH; // Load Halfword
                    RV32I_F3_LW: instruction_packet.alu_op = ALU_OP_LW; // Load Word
                    RV32I_F3_LBU: instruction_packet.alu_op = ALU_OP_LBU; // Load Byte Unsigned
                    RV32I_F3_LHU: instruction_packet.alu_op = ALU_OP_LHU; // Load Halfword Unsigned
                    default: instruction_packet.alu_op = ALU_OP_NOP;
                endcase
            end
            RV32I_STORE: begin
                // Store instructions
                instruction_packet.rs1_value = instruction[19:15];
                instruction_packet.rs2_value = instruction[24:20];
                instruction_packet.imm32 = {{20{instruction[31]}}, instruction[31:25], instruction[11:7]};
                case (funct3)
                    RV32I_F3_SB: instruction_packet.alu_op = ALU_OP_SB; // Store Byte
                    RV32I_F3_SH: instruction_packet.alu_op = ALU_OP_SH; // Store Halfword
                    RV32I_F3_SW: instruction_packet.alu_op = ALU_OP_SW; // Store Word
                    default: instruction_packet.alu_op = ALU_OP_NOP;
                endcase
            end
            RV32I_OP_IMM: begin
                // Immediate ALU operations
                instruction_packet.rs1_value = instruction[19:15];
                instruction_packet.rd_value = instruction[11:7];
                instruction_packet.imm32 = {{21{instruction[31]}}, instruction[30:20]};
                case (funct3)
                    RV32I_F3_ADDI: instruction_packet.alu_op = ALU_OP_ADDI; // Add Immediate
                    RV32I_F3_SLTI: instruction_packet.alu_op = ALU_OP_SLTI; // Set Less Than Immediate
                    RV32I_F3_SLTIU: instruction_packet.alu_op = ALU_OP_SLTIU; // Set Less Than Immediate Unsigned
                    RV32I_F3_XORI: instruction_packet.alu_op = ALU_OP_XORI; // XOR Immediate
                    RV32I_F3_ORI: instruction_packet.alu_op = ALU_OP_ORI; // OR Immediate
                    RV32I_F3_ANDI: instruction_packet.alu_op = ALU_OP_ANDI; // AND Immediate
                    RV32I_F3_SLLI: instruction_packet.alu_op = ALU_OP_SLLI; // Shift Left Logical Immediate
                    RV32I_F3_SRLI: instruction_packet.alu_op = ALU_OP_SRLI; // Shift Right Logical Immediate
                    RV32I_F3_SRAI: instruction_packet.alu_op = ALU_OP_SRAI; // Shift Right Arithmetic Immediate
                    default: instruction_packet.alu_op = ALU_OP_NOP;
                endcase
            end
            RV32I_OP_ALU: begin
                // Register-register ALU operations
                instruction_packet.rs1_value = instruction[19:15];
                instruction_packet.rs2_value = instruction[24:20];
                instruction_packet.rd_value = instruction[11:7];
                case ({funct7, funct3})
                    {RV32I_F7_ADD, RV32I_F3_ADD}: instruction_packet.alu_op = ALU_OP_ADD; // Add
                    {RV32I_F7_SUB, RV32I_F3_SUB}: instruction_packet.alu_op = ALU_OP_SUB; // Subtract
                    {RV32I_F7_SLT, RV32I_F3_SLT}: instruction_packet.alu_op = ALU_OP_SLT; // Set Less Than
                    {RV32I_F7_SLTU, RV32I_F3_SLTU}: instruction_packet.alu_op = ALU_OP_SLTU; // Set Less Than Unsigned
                    {RV32I_F7_XOR, RV32I_F3_XOR}: instruction_packet.alu_op = ALU_OP_XOR; // XOR
                    {RV32I_F7_OR, RV32I_F3_OR}: instruction_packet.alu_op = ALU_OP_OR; // OR
                    {RV32I_F7_AND, RV32I_F3_AND}: instruction_packet.alu_op = ALU_OP_AND; // AND
                    {RV32I_F7_SLL, RV32I_F3_SLL}: instruction_packet.alu_op = ALU_OP_SLL; // Shift Left Logical
                    {RV32I_F7_SRL, RV32I_F3_SRL}: instruction_packet.alu_op = ALU_OP_SRL; // Shift Right Logical
                    {RV32I_F7_SRA, RV32I_F3_SRA}: instruction_packet.alu_op = ALU_OP_SRA; // Shift Right Arithmetic

                    // RISC-V M-extension (Multiply/Divide)
                    {RV32M_F7_MUL, RV32M_F3_MUL}: instruction_packet.alu_op = ALU_OP_MUL; // Multiply
                    {RV32M_F7_MULH, RV32M_F3_MULH}: instruction_packet.alu_op = ALU_OP_MULH; // Multiply High
                    {RV32M_F7_MULHSU, RV32M_F3_MULHSU}: instruction_packet.alu_op = ALU_OP_MULHSU; // Multiply High Signed-Unsigned
                    {RV32M_F7_MULHU, RV32M_F3_MULHU}: instruction_packet.alu_op = ALU_OP_MULHU; // Multiply High Unsigned
                    {RV32M_F7_DIV, RV32M_F3_DIV}: instruction_packet.alu_op = ALU_OP_DIV; // Divide
                    {RV32M_F7_DIVU, RV32M_F3_DIVU}: instruction_packet.alu_op = ALU_OP_DIVU; // Divide Unsigned
                    {RV32M_F7_REM, RV32M_F3_REM}: instruction_packet.alu_op = ALU_OP_REM; // Remainder
                    {RV32M_F7_REMU, RV32M_F3_REMU}: instruction_packet.alu_op = ALU_OP_REMU; // Remainder Unsigned
                    default: instruction_packet.alu_op = ALU_OP_NOP;
                endcase
            end
            default: begin
                // Default case for unsupported opcodes
                instruction_packet.alu_op = ALU_OP_NOP;
            end
        endcase
    end
endmodule