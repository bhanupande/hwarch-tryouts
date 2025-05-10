// *****************************************************************************************
// File: rv32_pkg.sv
// Description: This package defines the instruction fields, control signals, and enums
//              for RISC-V RV32I and RV32M instruction decoding. It includes opcode,
//              funct3, and funct7 definitions, as well as ALU operation codes.
// Author: Bhanu Pande
// Date: May 9, 2025
// *****************************************************************************************

package rv32_pkg;
    // Issue packet structure
    typedef struct packed {
        logic [31:0] rs1_value; // Source register 1
        logic [31:0] rs2_value; // Source register 2
        logic [4:0] wb_sel;    // Destination register
        logic [31:0] imm32;    // Immediate value (if applicable)
        logic [5:0] alu_op;    // ALU operation code
    } rv32_issue_packet_t;

    // Define writeback packet structure
    typedef struct packed {
        logic [4:0] wb_sel;    // Destination register
        logic [31:0] wb_data;    // Data to write back
        logic wb_en; // Write enable signal
    } rv32_writeback_packet_t;

    // Define instruction fields using typedef
    typedef struct packed {
        logic [5:0] alu_op;      // ALU operation code
        logic [4:0] rd_sel;    // Destination register
        logic [4:0] rs1_sel;   // Source register 1
        logic [4:0] rs2_sel;   // Source register 2
        logic [31:0] imm32;      // Immediate value (if applicable)
    } rv32_instr_packet_t;

    // Define ALU operation codes
    typedef enum logic [5:0] {
        ALU_OP_ADD = 6'd0,       // Addition
        ALU_OP_SUB = 6'd1,       // Subtraction
        ALU_OP_SLL = 6'd2,       // Logical left shift
        ALU_OP_SLT = 6'd3,       // Set less than (signed)
        ALU_OP_SLTU = 6'd4,      // Set less than (unsigned)
        ALU_OP_XOR = 6'd5,       // Bitwise XOR
        ALU_OP_SRL = 6'd6,       // Logical right shift
        ALU_OP_SRA = 6'd7,       // Arithmetic right shift
        ALU_OP_OR = 6'd8,        // Bitwise OR
        ALU_OP_AND = 6'd9,       // Bitwise AND

        // Immediate operations
        ALU_OP_ADDI = 6'd10,     // Add immediate
        ALU_OP_SLTI = 6'd11,     // Set less than immediate (signed)
        ALU_OP_SLTIU = 6'd12,    // Set less than immediate (unsigned)
        ALU_OP_XORI = 6'd13,     // XOR immediate
        ALU_OP_ORI = 6'd14,      // OR immediate
        ALU_OP_ANDI = 6'd15,     // AND immediate
        ALU_OP_SLLI = 6'd16,     // Logical left shift immediate
        ALU_OP_SRLI = 6'd17,     // Logical right shift immediate
        ALU_OP_SRAI = 6'd18,     // Arithmetic right shift immediate

        // Load operations
        ALU_OP_LB = 6'd19,       // Load byte
        ALU_OP_LH = 6'd20,       // Load halfword
        ALU_OP_LW = 6'd21,       // Load word
        ALU_OP_LBU = 6'd22,      // Load byte unsigned
        ALU_OP_LHU = 6'd23,      // Load halfword unsigned

        // Store operations
        ALU_OP_SB = 6'd24,       // Store byte
        ALU_OP_SH = 6'd25,       // Store halfword
        ALU_OP_SW = 6'd26,       // Store word

        // Branch operations
        ALU_OP_BEQ = 6'd27,      // Branch if equal
        ALU_OP_BNE = 6'd28,      // Branch if not equal
        ALU_OP_BLT = 6'd29,      // Branch if less than (signed)
        ALU_OP_BGE = 6'd30,      // Branch if greater or equal (signed)
        ALU_OP_BLTU = 6'd31,     // Branch if less than (unsigned)
        ALU_OP_BGEU = 6'd32,     // Branch if greater or equal (unsigned)

        // Jump operations
        ALU_OP_JAL = 6'd33,      // Jump and link
        ALU_OP_JALR = 6'd34,     // Jump and link register

        // Upper immediate operations
        ALU_OP_LUI = 6'd35,      // Load upper immediate
        ALU_OP_AUIPC = 6'd36,    // Add upper immediate to PC

        // Multiply and divide operations (RV32M)
        ALU_OP_MUL = 6'd37,      // Multiply
        ALU_OP_MULH = 6'd38,     // Multiply high (signed)
        ALU_OP_MULHSU = 6'd39,   // Multiply high (signed x unsigned)
        ALU_OP_MULHU = 6'd40,    // Multiply high (unsigned)
        ALU_OP_DIV = 6'd41,      // Divide (signed)
        ALU_OP_DIVU = 6'd42,     // Divide (unsigned)
        ALU_OP_REM = 6'd43,      // Remainder (signed)
        ALU_OP_REMU = 6'd44,     // Remainder (unsigned)

        ALU_OP_NOP = 6'd63       // No operation
    } alu_op_t;

    // Define RV32I opcode values
    typedef enum logic [6:0] {
        RV32I_LUI = 7'b0110111,      // Load upper immediate
        RV32I_AUIPC = 7'b0010111,    // Add upper immediate to PC
        RV32I_JAL = 7'b1101111,      // Jump and link
        RV32I_JALR = 7'b1100111,     // Jump and link register
        RV32I_BRANCH = 7'b1100011,   // Branch instructions
        RV32I_LOAD = 7'b0000011,     // Load instructions
        RV32I_STORE = 7'b0100011,    // Store instructions
        RV32I_OP_IMM = 7'b0010011,   // Immediate ALU operations
        RV32I_OP_ALU = 7'b0110011,   // Register-register ALU operations
        RV32I_BARRIERS = 7'b0001111, // Memory barriers
        RV32I_SYSTEM = 7'b1110011    // System instructions
    } rv32_opcode_t;

    // Define RV32I funct7 values
    typedef enum logic [6:0] {
        RV32I_F7_IMM = 7'b0000000,   // Immediate operations
        RV32I_F7_ADD = 7'b0000000,   // Addition
        RV32I_F7_SUB = 7'b0100000,   // Subtraction
        RV32I_F7_SLL = 7'b0000000,   // Logical left shift
        RV32I_F7_SLT = 7'b0000000,   // Set less than (signed)
        RV32I_F7_SLTU = 7'b0000000,  // Set less than (unsigned)
        RV32I_F7_XOR = 7'b0000000,   // Bitwise XOR
        RV32I_F7_SRL = 7'b0000000,   // Logical right shift
        RV32I_F7_SRA = 7'b0100000,   // Arithmetic right shift
        RV32I_F7_OR = 7'b0000000,    // Bitwise OR
        RV32I_F7_AND = 7'b0000000,   // Bitwise AND
        RV32M_F7_MUL = 7'b0000001,   // Multiply
        RV32M_F7_MULH = 7'b0000001,  // Multiply high (signed)
        RV32M_F7_MULHSU = 7'b0000001,// Multiply high (signed x unsigned)
        RV32M_F7_MULHU = 7'b0000001, // Multiply high (unsigned)
        RV32M_F7_DIV = 7'b0000001,   // Divide (signed)
        RV32M_F7_DIVU = 7'b0000001,  // Divide (unsigned)
        RV32M_F7_REM = 7'b0000001,   // Remainder (signed)
        RV32M_F7_REMU = 7'b0000001   // Remainder (unsigned)
    } rv32_funct7_t;

    // Define RV32I funct3 values
    typedef enum logic [2:0] {
        RV32I_F3_ADDI = 3'b000,      // Add immediate
        RV32I_F3_SLTI = 3'b010,      // Set less than immediate (signed)
        RV32I_F3_SLTIU = 3'b011,     // Set less than immediate (unsigned)
        RV32I_F3_XORI = 3'b100,      // XOR immediate
        RV32I_F3_ORI = 3'b110,       // OR immediate
        RV32I_F3_ANDI = 3'b111,      // AND immediate
        RV32I_F3_SLLI = 3'b001,      // Logical left shift immediate
        RV32I_F3_SRLI = 3'b101,      // Logical right shift immediate
        RV32I_F3_SRAI = 3'b101,      // Arithmetic right shift immediate
        RV32I_F3_ADD = 3'b000,       // Addition
        RV32I_F3_SUB = 3'b000,       // Subtraction
        RV32I_F3_SLL = 3'b001,       // Logical left shift
        RV32I_F3_SLT = 3'b010,       // Set less than (signed)
        RV32I_F3_SLTU = 3'b011,      // Set less than (unsigned)
        RV32I_F3_XOR = 3'b100,       // Bitwise XOR
        RV32I_F3_SRL = 3'b101,       // Logical right shift
        RV32I_F3_SRA = 3'b101,       // Arithmetic right shift
        RV32I_F3_OR = 3'b110,        // Bitwise OR
        RV32I_F3_AND = 3'b111,       // Bitwise AND
        RV32M_F3_MUL = 3'b000,       // Multiply
        RV32M_F3_MULH = 3'b001,      // Multiply high (signed)
        RV32M_F3_MULHSU = 3'b010,    // Multiply high (signed x unsigned)
        RV32M_F3_MULHU = 3'b011,     // Multiply high (unsigned)
        RV32M_F3_DIV = 3'b100,       // Divide (signed)
        RV32M_F3_DIVU = 3'b101,      // Divide (unsigned)
        RV32M_F3_REM = 3'b110,       // Remainder (signed)
        RV32M_F3_REMU = 3'b111       // Remainder (unsigned)
    } rv32_funct3_t;

endpackage : rv32_pkg

