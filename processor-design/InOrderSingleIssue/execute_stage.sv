//-----------------------------------------------------------------------------
// File: execute_stage.sv
// Description: This module implements the execute stage of a RISC-V processor.
//              It performs ALU operations, memory access control, and branching.
// Author: Bhanu Pande
// Date: May 9, 2025
//-----------------------------------------------------------------------------

import rv32_pkg::*; // Import the package for constants and types

module execute_stage (
    input rv32_issue_packet_t issued_instruction_packet, // Decoded instruction packet
    input rv32_fwd_packet_t fwd_packet,                 // Forwarding packet for data hazards
    output rv32_branch_packet_t branch_packet,           // Branch packet output
    output rv32_mem_packet_t mem_packet,                 // Memory access packet output
    output rv32_ex2mem_wb_packet_t wb_packet,            // Write-back packet output
    output rv32_ex_control_packet_t ex_control_packet    // Control signals for memory operations
);

    // ***********************************************************************
    // Internal Signals
    // ***********************************************************************
    logic [31:0] rs1_value;       // Source register 1 value
    logic [31:0] rs2_value;       // Source register 2 value
    logic [31:0] imm32;           // Immediate value
    logic [5:0] alu_op;           // ALU operation code
    logic [31:0] pc_out;          // Program Counter output
    logic [31:0] pc_in;           // Program Counter input
    logic [31:0] alu_result;      // ALU result

    // ***********************************************************************
    // Assign Values from the Issue Packet
    // ***********************************************************************
    // Forwarding logic: Use forwarded data if enabled, otherwise use values from the issue packet
    assign rs1_value = fwd_packet.fwd_rs1_enable ? fwd_packet.fwd_rs1_data : issued_instruction_packet.rs1_value;
    assign rs2_value = fwd_packet.fwd_rs2_enable ? fwd_packet.fwd_rs2_data : issued_instruction_packet.rs2_value;
    assign imm32 = issued_instruction_packet.imm32; // Immediate value
    assign alu_op = issued_instruction_packet.alu_op; // ALU operation code
    assign pc_in = issued_instruction_packet.pc; // Program Counter input

    // ***********************************************************************
    // Write-back Packet Assignments
    // ***********************************************************************
    // Populate the write-back packet with appropriate values
    assign wb_packet.valid_opcode = issued_instruction_packet.valid_opcode; // Valid opcode for write-back
    assign wb_packet.rs1_sel = issued_instruction_packet.rs1_sel; // Source register 1 selection
    assign wb_packet.rs2_sel = issued_instruction_packet.rs2_sel; // Source register 2 selection
    assign wb_packet.wb_addr = issued_instruction_packet.rd_sel; // Destination register
    assign wb_packet.wb_pc = pc_out; // Program counter for write-back
    assign wb_packet.wb_data = alu_result; // Data to write back to register file
    assign wb_packet.wb_enable = (alu_op != ALU_OP_BEQ) && (alu_op != ALU_OP_BGEU) &&
                                  (alu_op != ALU_OP_BNE) && (alu_op != ALU_OP_BLT) &&
                                  (alu_op != ALU_OP_BGE) && (alu_op != ALU_OP_BLTU) &&
                                  (alu_op != ALU_OP_SB) && (alu_op != ALU_OP_SH) &&
                                  (alu_op != ALU_OP_SW); // Enable register write for non-branch and non-store operations

    // ***********************************************************************
    // Branch Packet Assignments
    // ***********************************************************************
    // Populate the branch packet with branch-related information
    assign branch_packet.branch_pc = issued_instruction_packet.pc; // Current PC
    assign branch_packet.branch_target = pc_out; // Branch target address
    assign branch_packet.branch_taken = (alu_op == ALU_OP_BEQ && rs1_value == rs2_value) || // Branch if equal
                                        (alu_op == ALU_OP_BNE && rs1_value != rs2_value) || // Branch if not equal
                                        (alu_op == ALU_OP_BLT && $signed(rs1_value) < $signed(rs2_value)) || // Branch if less than
                                        (alu_op == ALU_OP_BGE && $signed(rs1_value) >= $signed(rs2_value)) || // Branch if greater or equal
                                        (alu_op == ALU_OP_BLTU && rs1_value < rs2_value) || // Branch if less than unsigned
                                        (alu_op == ALU_OP_BGEU && rs1_value >= rs2_value); // Branch if greater or equal unsigned
    assign branch_packet.branch_type = (alu_op == ALU_OP_BEQ) ? 3'b000 : // Branch type encoding
                                       (alu_op == ALU_OP_BNE) ? 3'b001 :
                                       (alu_op == ALU_OP_BLT) ? 3'b010 :
                                       (alu_op == ALU_OP_BGE) ? 3'b011 :
                                       (alu_op == ALU_OP_BLTU) ? 3'b100 :
                                       (alu_op == ALU_OP_BGEU) ? 3'b101 : 3'b000; // Default to no branch

    // ***********************************************************************
    // Memory Packet Assignments
    // ***********************************************************************
    // Populate the memory packet with load/store operation details
    assign mem_packet.read_enable = (alu_op == ALU_OP_LB) || (alu_op == ALU_OP_LH) || (alu_op == ALU_OP_LW) ||
                                    (alu_op == ALU_OP_LBU) || (alu_op == ALU_OP_LHU); // Enable memory read for load operations
    assign mem_packet.write_enable = (alu_op == ALU_OP_SB) || (alu_op == ALU_OP_SH) || (alu_op == ALU_OP_SW); // Enable memory write for store operations
    assign mem_packet.addr = ((alu_op == ALU_OP_LB) || (alu_op == ALU_OP_LH) || (alu_op == ALU_OP_LW) ||
                              (alu_op == ALU_OP_LBU) || (alu_op == ALU_OP_LHU) ||
                              (alu_op == ALU_OP_SB) || (alu_op == ALU_OP_SH) || (alu_op == ALU_OP_SW)) ?
                              rs1_value + imm32 : 32'b0; // Calculate memory address for load/store operations
    assign mem_packet.data = (alu_op == ALU_OP_SB) ? {24'b0, rs2_value[7:0]} : // Store byte
                             (alu_op == ALU_OP_SH) ? {16'b0, rs2_value[15:0]} : // Store halfword
                             (alu_op == ALU_OP_SW) ? rs2_value : 32'b0; // Store word

    // ***********************************************************************
    // Control Packet Assignments
    // ***********************************************************************
    // Populate the control packet with load/store type information
    assign ex_control_packet.load_type = (alu_op == ALU_OP_LB) ? 3'b000 : // Load Byte
                                         (alu_op == ALU_OP_LH) ? 3'b001 : // Load Halfword
                                         (alu_op == ALU_OP_LW) ? 3'b010 : // Load Word
                                         (alu_op == ALU_OP_LBU) ? 3'b011 : // Load Byte Unsigned
                                         (alu_op == ALU_OP_LHU) ? 3'b100 : 3'b000; // Default to Load Byte
    assign ex_control_packet.store_type = (alu_op == ALU_OP_SB) ? 2'b00 : // Store Byte
                                          (alu_op == ALU_OP_SH) ? 2'b01 : // Store Halfword
                                          (alu_op == ALU_OP_SW) ? 2'b10 : 2'b00; // Default to Store Byte

    // ***********************************************************************
    // ALU Operation Logic
    // ***********************************************************************
    always_comb begin
        // Default values
        pc_out = pc_in;       // Default PC increment
        alu_result = 32'b0;   // Default ALU result

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
            ALU_OP_ADD: alu_result = rs1_value + rs2_value; // Addition
            ALU_OP_SUB: alu_result = rs1_value - rs2_value; // Subtraction
            ALU_OP_SLL: alu_result = rs1_value << rs2_value[4:0]; // Logical left shift
            ALU_OP_SLT: alu_result = ($signed(rs1_value) < $signed(rs2_value)) ? 1 : 0; // Set less than (signed)
            ALU_OP_SLTU: alu_result = (rs1_value < rs2_value) ? 1 : 0; // Set less than (unsigned)
            ALU_OP_XOR: alu_result = rs1_value ^ rs2_value; // Bitwise XOR
            ALU_OP_SRL: alu_result = rs1_value >> rs2_value[4:0]; // Logical right shift
            ALU_OP_SRA: alu_result = $signed(rs1_value) >>> rs2_value[4:0]; // Arithmetic right shift
            ALU_OP_OR: alu_result = rs1_value | rs2_value; // Bitwise OR
            ALU_OP_AND: alu_result = rs1_value & rs2_value; // Bitwise AND

            // Immediate operations
            ALU_OP_ADDI: alu_result = rs1_value + imm32; // Add immediate
            ALU_OP_SLTI: alu_result = ($signed(rs1_value) < $signed(imm32)) ? 1 : 0; // Set less than immediate (signed)
            ALU_OP_SLTIU: alu_result = (rs1_value < imm32) ? 1 : 0; // Set less than immediate (unsigned)
            ALU_OP_XORI: alu_result = rs1_value ^ imm32; // Bitwise XOR immediate
            ALU_OP_ORI: alu_result = rs1_value | imm32; // Bitwise OR immediate
            ALU_OP_ANDI: alu_result = rs1_value & imm32; // Bitwise AND immediate
            ALU_OP_SLLI: alu_result = rs1_value << imm32[4:0]; // Logical left shift immediate
            ALU_OP_SRLI: alu_result = rs1_value >> imm32[4:0]; // Logical right shift immediate
            ALU_OP_SRAI: alu_result = $signed(rs1_value) >>> imm32[4:0]; // Arithmetic right shift immediate

            // Upper immediate operations
            ALU_OP_LUI: alu_result = {imm32[31:12], 12'b0}; // Load Upper Immediate
            ALU_OP_AUIPC: alu_result = pc_in + {imm32[31:12], 12'b0}; // Add Upper Immediate to PC

            // Load and Store operations
            ALU_OP_LB, ALU_OP_LH, ALU_OP_LW, ALU_OP_LBU, ALU_OP_LHU,
            ALU_OP_SB, ALU_OP_SH, ALU_OP_SW: alu_result = rs1_value + imm32; // Calculate memory address

            // Branch operations
            ALU_OP_BEQ, ALU_OP_BNE, ALU_OP_BLT, ALU_OP_BGE, ALU_OP_BLTU, ALU_OP_BGEU: begin
                alu_result = (branch_packet.branch_taken) ? pc_in + imm32 : pc_in; // Branch if condition met
                pc_out = alu_result; // Update PC output
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
            default: begin
                alu_result = 32'b0; // Default to zero
                pc_out = pc_in; // Default PC increment
            end
        endcase
    end

endmodule