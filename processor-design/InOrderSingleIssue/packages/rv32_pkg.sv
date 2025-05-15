// *****************************************************************************************
// File:        rv32_pkg.sv
// Description: RISC-V RV32I/RV32M package. Defines instruction fields, control signals,
//              enums, and pipeline packet structures for decoding and datapath control.
// Author:      Bhanu Pande
// Date:        May 9, 2025
// Revision:    1.0
// *****************************************************************************************

package rv32_pkg;

    // *****************************************************************************************
    // ALU Operation Codes
    // Enumerates all ALU operations, including arithmetic, logical, load/store,
    // branch, jump, and multiply/divide (RV32M) operations.
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
    // Enumerates opcode values for RISC-V RV32I instructions.
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
    // Enumerates funct7 values for RISC-V RV32I instructions.
    // *****************************************************************************************
    typedef enum logic [6:0] {
        RV32I_F7_ADD    = 7'b0000000, // Addition
        RV32I_F7_SUB    = 7'b0100000, // Subtraction
        RV32M_F7_MUL    = 7'b0000001  // Multiply
    } rv32_funct7_t;

    // *****************************************************************************************
    // RV32I Funct3 Values
    // Enumerates funct3 values for RISC-V RV32I instructions.
    // Used to differentiate between ALU operations and other instruction types.
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

    // *****************************************************************************************
    // Forwarding Packet Structure
    // Used for forwarding data between pipeline stages to resolve hazards.
    // *****************************************************************************************
    typedef struct packed {
        logic [31:0] fwd_rs1_data; // Forwarded data for source register 1
        logic [31:0] fwd_rs2_data; // Forwarded data for source register 2
        logic        fwd_rs1_enable; // Forwarding enable for rs1
        logic        fwd_rs2_enable; // Forwarding enable for rs2
    } rv32_fwd_packet_t;

    // *****************************************************************************************
    // EX Control Packet Structure
    // Control signals for the execute stage (e.g., load/store type).
    // *****************************************************************************************
    typedef struct packed {
        logic [2:0] load_type;  // Load operation type (LB, LH, LW, etc.)
        logic [1:0] store_type; // Store operation type (SB, SH, SW)
    } rv32_ex_control_packet_t;

    // *****************************************************************************************
    // Write-Back Packet Structure (EX to MEM)
    // Data passed from the execute stage to the memory stage.
    // *****************************************************************************************
    typedef struct packed {
        logic [4:0]  wb_addr;      // Register address to write back
        logic [31:0] wb_data;      // Data to write back
        logic        wb_enable;    // Write-back enable
        logic [31:0] wb_pc;        // Program counter for the instruction
        logic [4:0]  rs1_sel;      // Source register 1 selection
        logic [4:0]  rs2_sel;      // Source register 2 selection
        logic        valid_opcode; // Valid opcode signal
        logic        dont_forward; // Don't forward signal
    } rv32_ex2mem_wb_packet_t;

    // *****************************************************************************************
    // Write-Back Packet Structure (MEM to WB)
    // Data passed from the memory stage to the write-back stage.
    // *****************************************************************************************
    typedef struct packed {
        logic [4:0]  wb_addr;      // Register address to write back
        logic [31:0] wb_data;      // Data to write back
        logic        wb_enable;    // Write-back enable
        logic [31:0] wb_pc;        // Program counter for the instruction
        logic [4:0]  rs1_sel;      // Source register 1 selection
        logic [4:0]  rs2_sel;      // Source register 2 selection
        logic        valid_opcode; // Valid opcode signal
        logic        dont_forward; // Don't forward signal
        logic        is_load;      // Load operation flag
        logic        is_store;     // Store operation flag
    } rv32_mem2wb_packet_t;

    // *****************************************************************************************
    // Memory Access Packet Structure
    // Signals for memory read/write operations.
    // *****************************************************************************************
    typedef struct packed {
        logic [31:0] addr;         // Memory address
        logic [31:0] data;         // Data to be written or read
        logic        read_enable;  // Read enable signal
        logic        write_enable; // Write enable signal
        logic        is_load;      // Load operation flag
        logic        is_store;     // Store operation flag
    } rv32_mem_packet_t;

    // *****************************************************************************************
    // Branch Packet Structure
    // Signals for branch operations in the pipeline.
    // *****************************************************************************************
    typedef struct packed {
        logic [2:0]  branch_type;    // Branch type (e.g., BEQ, BNE)
        logic [31:0] branch_pc;      // Program counter for branch instruction
        logic [31:0] branch_target;  // Branch target address
        logic        branch_taken;   // Branch taken signal
    } rv32_branch_packet_t;

    // *****************************************************************************************
    // Instruction Packet Structure
    // Fields for decoded instructions in the pipeline.
    // *****************************************************************************************
    typedef struct packed {
        alu_op_t     alu_op;         // ALU operation code
        logic [4:0]  rd_sel;         // Destination register
        logic [4:0]  rs1_sel;        // Source register 1
        logic [4:0]  rs2_sel;        // Source register 2
        logic [31:0] imm32;          // Immediate value (if applicable)
        logic [31:0] pc;             // Program counter
        logic        valid_opcode;   // Valid opcode signal
        logic        dont_forward;   // Don't forward signal
    } rv32_instr_packet_t;

    // *****************************************************************************************
    // Issue Packet Structure
    // Fields for issuing instructions to the execute stage.
    // *****************************************************************************************
    typedef struct packed {
        alu_op_t     alu_op;         // ALU operation code
        logic [4:0]  rd_sel;         // Destination register
        logic [4:0]  rs1_sel;        // Source register 1
        logic [4:0]  rs2_sel;        // Source register 2
        logic [31:0] imm32;          // Immediate value (if applicable)
        logic [31:0] pc;             // Program counter
        logic [31:0] rs1_value;      // Value of source register 1
        logic [31:0] rs2_value;      // Value of source register 2
        logic        valid_opcode;   // Valid opcode signal
        logic        dont_forward;   // Don't forward signal
    } rv32_issue_packet_t;

    // *****************************************************************************************
    // IF-OF Packet Structure
    // Fields for passing data from the instruction fetch stage to the decode stage.
    // *****************************************************************************************
    typedef struct packed {
        logic [31:0] pc;          // Program counter
        logic [31:0] instruction; // Instruction fetched
    } rv32_if_packet_t;

    // ***********************************************************************
    // Function: dont_forward
    // Returns 1 if the instruction should not be forwarded (e.g., NOP).
    // ***********************************************************************
    function logic dont_forward(input [31:0] instruction);
    begin
        case (instruction[31:0])
            32'h00000013: // NOP
                dont_forward = 1'b1;
            default:
                dont_forward = 1'b0;
        endcase
    end
    endfunction

    // ***********************************************************************
    // Function: is_valid_opcode
    // Returns 1 if the opcode is a valid RV32I opcode.
    // Used to filter out illegal or reserved opcodes during decode.
    // ***********************************************************************
    function logic is_valid_opcode(input rv32_opcode_t opcode);
    begin
        case (opcode)
            7'b0110111, // LUI
            7'b0010111, // AUIPC
            7'b1101111, // JAL
            7'b1100111, // JALR
            7'b1100011, // BRANCH
            7'b0000011, // LOAD
            7'b0100011, // STORE
            7'b0010011, // OP-IMM
            7'b0110011, // OP
            7'b0001111, // FENCE
            7'b1110011: // SYSTEM
                is_valid_opcode = 1'b1; // Recognized as valid
            default:
                is_valid_opcode = 1'b0; // Not a valid opcode
        endcase
    end
    endfunction

    // ***********************************************************************
    // Function: no_dependency
    // Returns 1 if the opcode does not create data dependencies.
    // Used to identify instructions that do not write to registers,
    // such as branches, fences, and system instructions.
    // ***********************************************************************
    function logic no_dependency(input rv32_opcode_t opcode);
    begin
        case (opcode)
            7'b1100011, // BRANCH: Conditional branch instructions (BEQ, BNE, etc.)
            7'b0001111, // FENCE:  Memory barrier instructions (FENCE, FENCE.I)
            7'b1110011: // SYSTEM: System instructions (ECALL, EBREAK, CSR)
                no_dependency = 1'b1; // No data dependency, does not write to registers
            default:
                no_dependency = 1'b0; // May have data dependency (writes to registers)
        endcase
    end
    endfunction
    // ***********************************************************************

    // ***********************************************************************
    // Function: half_add
    // Returns a 2-bit result of a half adder for two input bits.
    // half_add[0] = sum (a XOR b)
    // half_add[1] = carry (a AND b)
    // ***********************************************************************
    function logic [1:0] half_add (input logic a, input logic b);
        begin
            half_add[0] = a ^ b; // Sum bit: XOR of inputs
            half_add[1] = a & b; // Carry bit: AND of inputs
        end
    endfunction

    // ***********************************************************************
    // Function: cla
    // Returns a 3-bit result for a 1-bit carry lookahead adder.
    // cla[0] = a XOR b (sum without carry-in)
    // cla[1] = a AND b (carry generate)
    // cla[2] = (a XOR b) XOR c (sum with carry-in)
    // ***********************************************************************
    function logic [2:0] cla (input logic a, input logic b, input logic c);
        begin
            cla[0] = a ^ b;       // Propagate: XOR of a and b
            cla[1] = a & b;       // Generate: AND of a and b
            cla[2] = cla[0] ^ c;  // Sum with carry-in
        end
    endfunction
endpackage : rv32_pkg

