// *****************************************************************************************
// File:        of_stage.sv
// Description: This module implements the decode (Operand Fetch) stage of a RISC-V processor.
//              It decodes the 32-bit instruction into control signals and instruction packet fields
//              such as source registers, destination register, immediate values, and ALU operation.
// Author:      Bhanu Pande
// Date:        May 9, 2025
// *****************************************************************************************

import rv32_pkg::*; // Import the package for constants and types

// *****************************************************************************************
// Module:      of_stage
// Inputs:
//   - if_packet: Input packet containing the 32-bit RISC-V instruction and PC.
// Outputs:
//   - instruction_packet: Struct containing decoded instruction fields (rs1, rs2, rd, imm, alu_op).
// *****************************************************************************************
module of_stage (
    input  rv32_if_packet_t if_packet,             // Input packet containing instruction and PC
    output rv32_instr_packet_t instruction_packet  // Decoded instruction packet
);

    // =========================================================================
    // Field Extraction
    // =========================================================================
    // Extract opcode, funct3, and funct7 fields from the instruction
    rv32_opcode_t opcode;       // Opcode field (bits 6:0)
    rv32_funct3_t funct3;       // Funct3 field (bits 14:12)
    rv32_funct7_t funct7;       // Funct7 field (bits 31:25)
    logic [31:0] instruction;   // Instruction to be decoded

    // Assign instruction fields
    assign instruction = if_packet.instruction; // Get instruction from input packet
    assign opcode      = instruction[6:0];      // Extract opcode
    assign funct3      = instruction[14:12];    // Extract funct3
    assign funct7      = instruction[31:25];    // Extract funct7

    // =========================================================================
    // Instruction Decode Logic
    // =========================================================================
    // Combinational logic for decoding the instruction
    always_comb begin
        // Initialize outputs to default values
        instruction_packet = '{
            rs1_sel:      5'b0,                        // Default source register 1
            rs2_sel:      5'b0,                        // Default source register 2
            rd_sel:       5'b0,                        // Default destination register
            imm32:        32'b0,                       // Default immediate value
            alu_op:       ALU_OP_NOP,                  // Default ALU operation (No Operation)
            pc:           if_packet.pc,                // Pass through the program counter
            valid_opcode: is_valid_opcode(opcode),     // Check if opcode is valid
            dont_forward: dont_forward(instruction)    // Check if forwarding is needed
        };

        // Decode based on opcode
        case (opcode)
            // LUI: Load Upper Immediate
            RV32I_LUI: begin
                instruction_packet.rd_sel  = instruction[11:7];
                instruction_packet.imm32   = {instruction[31:12], 12'b0};
                instruction_packet.alu_op  = ALU_OP_LUI;
            end

            // AUIPC: Add Upper Immediate to PC
            RV32I_AUIPC: begin
                instruction_packet.rd_sel  = instruction[11:7];
                instruction_packet.imm32   = {instruction[31:12], 12'b0};
                instruction_packet.alu_op  = ALU_OP_AUIPC;
            end

            // JAL: Jump and Link
            RV32I_JAL: begin
                instruction_packet.rd_sel  = instruction[11:7];
                instruction_packet.imm32   = {{11{instruction[31]}}, instruction[19:12], instruction[20], instruction[30:21], 1'b0};
                instruction_packet.alu_op  = ALU_OP_JAL;
            end

            // JALR: Jump and Link Register
            RV32I_JALR: begin
                instruction_packet.rs1_sel = instruction[19:15];
                instruction_packet.rd_sel  = instruction[11:7];
                instruction_packet.imm32   = {{20{instruction[31]}}, instruction[30:20]};
                instruction_packet.alu_op  = ALU_OP_JALR;
            end

            // Branch instructions (BEQ, BNE, BLT, BGE, BLTU, BGEU)
            RV32I_BRANCH: begin
                instruction_packet.rs1_sel = instruction[19:15];
                instruction_packet.rs2_sel = instruction[24:20];
                instruction_packet.imm32   = {{20{instruction[31]}}, instruction[7], instruction[30:25], instruction[11:8], 1'b0};
                case (funct3)
                    RV32I_F3_ADD:  instruction_packet.alu_op = ALU_OP_BEQ;   // Branch if Equal
                    RV32I_F3_SLL:  instruction_packet.alu_op = ALU_OP_BNE;   // Branch if Not Equal
                    RV32I_F3_XOR:  instruction_packet.alu_op = ALU_OP_BLT;   // Branch if Less Than
                    RV32I_F3_SRL:  instruction_packet.alu_op = ALU_OP_BGE;   // Branch if Greater or Equal
                    RV32I_F3_OR:   instruction_packet.alu_op = ALU_OP_BLTU;  // Branch if Less Than Unsigned
                    RV32I_F3_AND:  instruction_packet.alu_op = ALU_OP_BGEU;  // Branch if Greater or Equal Unsigned
                    default:       instruction_packet.alu_op = ALU_OP_NOP;
                endcase
            end

            // Load instructions (LB, LH, LW, LBU, LHU)
            RV32I_LOAD: begin
                instruction_packet.rs1_sel = instruction[19:15];
                instruction_packet.rd_sel  = instruction[11:7];
                instruction_packet.imm32   = {{20{instruction[31]}}, instruction[31:20]};
                case (funct3)
                    RV32I_F3_ADD:  instruction_packet.alu_op = ALU_OP_LB;   // Load Byte
                    RV32I_F3_SLL:  instruction_packet.alu_op = ALU_OP_LH;   // Load Halfword
                    RV32I_F3_SLT:  instruction_packet.alu_op = ALU_OP_LW;   // Load Word
                    RV32I_F3_XOR:  instruction_packet.alu_op = ALU_OP_LBU;  // Load Byte Unsigned
                    RV32I_F3_SRL:  instruction_packet.alu_op = ALU_OP_LHU;  // Load Halfword Unsigned
                    default:       instruction_packet.alu_op = ALU_OP_NOP;
                endcase
            end

            // Store instructions (SB, SH, SW)
            RV32I_STORE: begin
                instruction_packet.rs1_sel = instruction[19:15];
                instruction_packet.rs2_sel = instruction[24:20];
                instruction_packet.imm32   = {{20{instruction[31]}}, instruction[31:25], instruction[11:7]};
                case (funct3)
                    RV32I_F3_ADD:  instruction_packet.alu_op = ALU_OP_SB;   // Store Byte
                    RV32I_F3_SLL:  instruction_packet.alu_op = ALU_OP_SH;   // Store Halfword
                    RV32I_F3_SLT:  instruction_packet.alu_op = ALU_OP_SW;   // Store Word
                    default:       instruction_packet.alu_op = ALU_OP_NOP;
                endcase
            end

            // Immediate ALU operations (ADDI, SLLI, SLTI, SLTIU, XORI, ORI, ANDI, SRLI, SRAI)
            RV32I_OP_IMM: begin
                instruction_packet.rs1_sel = instruction[19:15];
                instruction_packet.rd_sel  = instruction[11:7];
                instruction_packet.imm32   = {{21{instruction[31]}}, instruction[30:20]};
                case (funct3)
                    RV32I_F3_ADD:   instruction_packet.alu_op = ALU_OP_ADDI;   // Add Immediate
                    RV32I_F3_SLL:   instruction_packet.alu_op = ALU_OP_SLLI;   // Shift Left Logical Immediate
                    RV32I_F3_SLT:   instruction_packet.alu_op = ALU_OP_SLTI;   // Set Less Than Immediate
                    RV32I_F3_SLTU:  instruction_packet.alu_op = ALU_OP_SLTIU;  // Set Less Than Immediate Unsigned
                    RV32I_F3_XOR:   instruction_packet.alu_op = ALU_OP_XORI;   // XOR Immediate
                    RV32I_F3_OR:    instruction_packet.alu_op = ALU_OP_ORI;    // OR Immediate
                    RV32I_F3_AND:   instruction_packet.alu_op = ALU_OP_ANDI;   // AND Immediate
                    RV32I_F3_SRL: begin
                        case (funct7)
                            RV32I_F7_ADD: instruction_packet.alu_op = ALU_OP_SRLI; // Shift Right Logical Immediate
                            RV32I_F7_SUB: instruction_packet.alu_op = ALU_OP_SRAI; // Shift Right Arithmetic Immediate
                            default:      instruction_packet.alu_op = ALU_OP_NOP;
                        endcase
                    end
                    default: instruction_packet.alu_op = ALU_OP_NOP;
                endcase
            end

            // Register-register ALU operations (ADD, SUB, SLL, SLT, SLTU, XOR, OR, AND, SRL, SRA, MUL, DIV, REM, etc.)
            RV32I_OP_ALU: begin
                instruction_packet.rs1_sel = instruction[19:15];
                instruction_packet.rs2_sel = instruction[24:20];
                instruction_packet.rd_sel  = instruction[11:7];
                case (funct7)
                    RV32I_F7_ADD: begin
                        case (funct3)
                            RV32I_F3_ADD:   instruction_packet.alu_op = ALU_OP_ADD;   // Add
                            RV32I_F3_SLL:   instruction_packet.alu_op = ALU_OP_SLL;   // Shift Left Logical
                            RV32I_F3_SLT:   instruction_packet.alu_op = ALU_OP_SLT;   // Set Less Than
                            RV32I_F3_SLTU:  instruction_packet.alu_op = ALU_OP_SLTU;  // Set Less Than Unsigned
                            RV32I_F3_XOR:   instruction_packet.alu_op = ALU_OP_XOR;   // XOR
                            RV32I_F3_OR:    instruction_packet.alu_op = ALU_OP_OR;    // OR
                            RV32I_F3_AND:   instruction_packet.alu_op = ALU_OP_AND;   // AND
                            RV32I_F3_SRL:   instruction_packet.alu_op = ALU_OP_SRL;   // Shift Right Logical
                            default:        instruction_packet.alu_op = ALU_OP_NOP;
                        endcase
                    end
                    RV32I_F7_SUB: begin
                        case (funct3)
                            RV32I_F3_ADD:   instruction_packet.alu_op = ALU_OP_SUB;   // Subtract
                            RV32I_F3_SRL:   instruction_packet.alu_op = ALU_OP_SRA;   // Shift Right Arithmetic
                            default:        instruction_packet.alu_op = ALU_OP_NOP;
                        endcase
                    end
                    RV32M_F7_MUL: begin
                        case (funct3)
                            RV32I_F3_ADD:   instruction_packet.alu_op = ALU_OP_MUL;    // Multiply
                            RV32I_F3_SLL:   instruction_packet.alu_op = ALU_OP_MULH;   // Multiply High
                            RV32I_F3_SLT:   instruction_packet.alu_op = ALU_OP_MULHSU; // Multiply High Signed-Unsigned
                            RV32I_F3_SLTU:  instruction_packet.alu_op = ALU_OP_MULHU;  // Multiply High Unsigned
                            RV32I_F3_XOR:   instruction_packet.alu_op = ALU_OP_DIV;    // Divide
                            RV32I_F3_SRL:   instruction_packet.alu_op = ALU_OP_DIVU;   // Divide Unsigned
                            RV32I_F3_OR:    instruction_packet.alu_op = ALU_OP_REM;    // Remainder
                            RV32I_F3_AND:   instruction_packet.alu_op = ALU_OP_REMU;   // Remainder Unsigned
                            default:        instruction_packet.alu_op = ALU_OP_NOP;
                        endcase
                    end
                    default: instruction_packet.alu_op = ALU_OP_NOP;
                endcase
            end

            // Default case for unsupported or unimplemented opcodes
            default: begin
                instruction_packet.alu_op = ALU_OP_NOP;
            end
        endcase
    end

endmodule