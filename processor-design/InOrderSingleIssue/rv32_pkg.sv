// *****************************************************************************************
// File: rv32_pkg.sv
// Description: This package defines the instruction fields, control signals, and enums
//              for RISC-V RV32I and RV32M instruction decoding. It includes opcode,
//              funct3, and funct7 definitions, as well as ALU operation codes.
// Author: Bhanu Pande
// Date: May 9, 2025
// *****************************************************************************************

package rv32_pkg;

    // *****************************************************************************************
    // EX Control Packet Structure
    // Description: Defines control signals for the execute stage.
    // Fields:
    //   - load_type: Load operation type (e.g., LB, LH, LW).
    //   - store_type: Store operation type (e.g., SB, SH, SW).
    // *****************************************************************************************
    typedef struct packed {
        logic [2:0] load_type;  // Load select signal
        logic [1:0] store_type; // Store select signal
    } rv32_ex_control_packet_t;

    // *****************************************************************************************
    // Write-Back Packet Structures
    // Description: Defines packets for write-back data from EX to MEM and MEM to WB stages.
    // Fields:
    //   - wb_addr: Register address to write back.
    //   - wb_data: Data to write back.
    //   - wb_enable: Write-back enable signal.
    //   - wb_pc: Program counter for the instruction.
    // *****************************************************************************************
    typedef struct packed {
        logic [4:0] wb_addr;    // Register address to write back
        logic [31:0] wb_data;   // Data to write back
        logic wb_enable;        // Write-back enable signal
        logic [31:0] wb_pc;     // Program counter for the instruction
        logic [4:0] rs1_sel;    // Source register 1 selection
        logic [4:0] rs2_sel;    // Source register 2 selection
    } rv32_ex2mem_wb_packet_t;

    typedef struct packed {
        logic [4:0] wb_addr;    // Register address to write back
        logic [31:0] wb_data;   // Data to write back
        logic wb_enable;        // Write-back enable signal
        logic [31:0] wb_pc;     // Program counter for the instruction
        logic [4:0] rs1_sel;    // Source register 1 selection
        logic [4:0] rs2_sel;    // Source register 2 selection
    } rv32_mem2wb_packet_t;

    // *****************************************************************************************
    // Memory Access Packet Structure
    // Description: Defines signals for memory read/write operations.
    // Fields:
    //   - addr: Memory address.
    //   - data: Data to be written or read.
    //   - read_enable: Read enable signal.
    //   - write_enable: Write enable signal.
    // *****************************************************************************************
    typedef struct packed {
        logic [31:0] addr;         // Memory address
        logic [31:0] data;         // Data to be written or read
        logic read_enable;         // Read enable signal
        logic write_enable;        // Write enable signal
    } rv32_mem_packet_t;

    // *****************************************************************************************
    // Branch Packet Structure
    // Description: Defines signals for branch operations.
    // Fields:
    //   - branch_type: Branch type (e.g., BEQ, BNE).
    //   - branch_pc: Program counter for the branch instruction.
    //   - branch_target: Branch target address.
    //   - branch_taken: Branch taken signal.
    // *****************************************************************************************
    typedef struct packed {
        logic [2:0] branch_type;    // Branch type (e.g., BEQ, BNE)
        logic [31:0] branch_pc;     // Program counter for branch instruction
        logic [31:0] branch_target; // Branch target address
        logic branch_taken;         // Branch taken signal
    } rv32_branch_packet_t;

    // *****************************************************************************************
    // Instruction Packet Structure
    // Description: Defines fields for decoded instructions.
    // Fields:
    //   - alu_op: ALU operation code.
    //   - rd_sel: Destination register.
    //   - rs1_sel: Source register 1.
    //   - rs2_sel: Source register 2.
    //   - imm32: Immediate value.
    //   - pc: Program counter.
    // *****************************************************************************************
    typedef struct packed {
        logic [5:0] alu_op;      // ALU operation code
        logic [4:0] rd_sel;      // Destination register
        logic [4:0] rs1_sel;     // Source register 1
        logic [4:0] rs2_sel;     // Source register 2
        logic [31:0] imm32;      // Immediate value (if applicable)
        logic [31:0] pc;         // Program counter
    } rv32_instr_packet_t;

    // *****************************************************************************************
    // Issue Packet Structure
    // Description: Defines fields for issuing instructions to the execute stage.
    // Fields:
    //   - alu_op: ALU operation code.
    //   - rd_sel: Destination register.
    //   - imm32: Immediate value.
    //   - pc: Program counter.
    //   - rs1_value: Value of source register 1.
    //   - rs2_value: Value of source register 2.
    // *****************************************************************************************
    typedef struct packed {
        logic [5:0] alu_op;      // ALU operation code
        logic [4:0] rd_sel;      // Destination register
        logic [4:0] rs1_sel;     // Source register 1
        logic [4:0] rs2_sel;     // Source register 2
        logic [31:0] imm32;      // Immediate value (if applicable)
        logic [31:0] pc;         // Program counter
        logic [31:0] rs1_value;  // Value of source register 1
        logic [31:0] rs2_value;  // Value of source register 2
    } rv32_issue_packet_t;

    // *****************************************************************************************
    // IF-OF Packet Structure
    // Description: Defines fields for passing data from the instruction fetch stage to
    //              the decode stage.
    // Fields:
    //   - pc: Program counter.
    //   - instruction: Instruction fetched.
    // *****************************************************************************************
    typedef struct packed {
        logic [31:0] pc;          // Program counter
        logic [31:0] instruction; // Instruction fetched
    } rv32_if_packet_t;

    // *****************************************************************************************
    // ALU Operation Codes
    // Description: Enumerates all ALU operations, including arithmetic, logical, load/store,
    //              branch, and jump operations.
    // *****************************************************************************************
    typedef enum logic [5:0] {
        ALU_OP_ADD      = 6'd1,   // Addition
        ALU_OP_SUB      = 6'd2,   // Subtraction
        ALU_OP_SLL      = 6'd3,   // Logical left shift
        ALU_OP_SLT      = 6'd4,   // Set less than (signed)
        ALU_OP_SLTU     = 6'd5,   // Set less than (unsigned)
        ALU_OP_XOR      = 6'd6,   // Bitwise XOR
        ALU_OP_SRL      = 6'd7,   // Logical right shift
        ALU_OP_SRA      = 6'd8,   // Arithmetic right shift
        ALU_OP_OR       = 6'd9,   // Bitwise OR
        ALU_OP_AND      = 6'd10,  // Bitwise AND
        ALU_OP_NOP      = 6'd0,   // No operation
        // Immediate operations
        ALU_OP_ADDI     = 6'd11,  // Add immediate
        ALU_OP_SLLI     = 6'd12,  // Logical left shift immediate
        ALU_OP_SLTI     = 6'd13,  // Set less than immediate (signed)
        ALU_OP_SLTIU    = 6'd14,  // Set less than immediate (unsigned)
        ALU_OP_XORI     = 6'd15,  // XOR immediate
        ALU_OP_SRLI     = 6'd16,  // Logical right shift immediate
        ALU_OP_SRAI     = 6'd17,  // Arithmetic right shift immediate
        ALU_OP_ORI      = 6'd18,  // OR immediate
        ALU_OP_ANDI     = 6'd19,  // AND immediate
        // Load operations
        ALU_OP_LB       = 6'd20,  // Load byte
        ALU_OP_LH       = 6'd21,  // Load halfword
        ALU_OP_LW       = 6'd22,  // Load word
        ALU_OP_LBU      = 6'd23,  // Load byte unsigned
        ALU_OP_LHU      = 6'd24,  // Load halfword unsigned
        // Store operations
        ALU_OP_SB       = 6'd25,  // Store byte
        ALU_OP_SH       = 6'd26,  // Store halfword
        ALU_OP_SW       = 6'd27,  // Store word
        // Branch operations
        ALU_OP_BEQ      = 6'd28,  // Branch if equal
        ALU_OP_BNE      = 6'd29,  // Branch if not equal
        ALU_OP_BLT      = 6'd30,  // Branch if less than (signed)
        ALU_OP_BGE      = 6'd31,  // Branch if greater or equal (signed)
        ALU_OP_BLTU     = 6'd32,  // Branch if less than (unsigned)
        ALU_OP_BGEU     = 6'd33,  // Branch if greater or equal (unsigned)
        // Jump operations
        ALU_OP_JAL      = 6'd34,  // Jump and link
        ALU_OP_JALR     = 6'd35,  // Jump and link register
        // Upper immediate operations
        ALU_OP_LUI      = 6'd36,  // Load upper immediate
        ALU_OP_AUIPC    = 6'd37,  // Add upper immediate to PC
        // Multiply and divide operations (RV32M)
        ALU_OP_MUL      = 6'd38,  // Multiply
        ALU_OP_MULH     = 6'd39,  // Multiply high (signed)
        ALU_OP_MULHSU   = 6'd40,  // Multiply high (signed x unsigned)
        ALU_OP_MULHU    = 6'd41,  // Multiply high (unsigned)
        ALU_OP_DIV      = 6'd42,  // Divide (signed)
        ALU_OP_DIVU     = 6'd43,  // Divide (unsigned)
        ALU_OP_REM      = 6'd44,  // Remainder (signed)
        ALU_OP_REMU     = 6'd45   // Remainder (unsigned)
    } alu_op_t;

    // *****************************************************************************************
    // RV32I Opcode Values
    // Description: Enumerates opcode values for RISC-V RV32I instructions.
    // *****************************************************************************************
    typedef enum logic [6:0] {
        RV32I_LUI       = 7'b0110111, // Load upper immediate
        RV32I_AUIPC     = 7'b0010111, // Add upper immediate to PC
        RV32I_JAL       = 7'b1101111, // Jump and link
        RV32I_JALR      = 7'b1100111, // Jump and link register
        RV32I_BRANCH    = 7'b1100011, // Branch instructions
        RV32I_LOAD      = 7'b0000011, // Load instructions
        RV32I_STORE     = 7'b0100011, // Store instructions
        RV32I_OP_IMM    = 7'b0010011, // Immediate ALU operations
        RV32I_OP_ALU    = 7'b0110011, // Register-register ALU operations
        RV32I_BARRIERS  = 7'b0001111, // Memory barriers
        RV32I_SYSTEM    = 7'b1110011  // System instructions
    } rv32_opcode_t;

    // *****************************************************************************************
    // RV32I Funct7 Values
    // Description: Enumerates funct7 values for RISC-V RV32I instructions.
    // *****************************************************************************************
    typedef enum logic [6:0] {
        RV32I_F7_ADD    = 7'b0000000, // Addition
        RV32I_F7_SUB    = 7'b0100000, // Subtraction
        RV32M_F7_MUL    = 7'b0000001  // Multiply
    } rv32_funct7_t;

    // *****************************************************************************************
    // RV32I Funct3 Values
    // Description: Enumerates funct3 values for RISC-V RV32I instructions.
    // *****************************************************************************************
    typedef enum logic [2:0] {
        RV32I_F3_ADD    = 3'b000, // Addition
        RV32I_F3_SLL    = 3'b001, // Logical left shift
        RV32I_F3_SLT    = 3'b010, // Set less than (signed)
        RV32I_F3_SLTU   = 3'b011, // Set less than (unsigned)
        RV32I_F3_XOR    = 3'b100, // Bitwise XOR
        RV32I_F3_SRL    = 3'b101, // Logical right shift
        RV32I_F3_OR     = 3'b110, // Bitwise OR
        RV32I_F3_AND    = 3'b111  // Bitwise AND
    } rv32_funct3_t;

endpackage : rv32_pkg

