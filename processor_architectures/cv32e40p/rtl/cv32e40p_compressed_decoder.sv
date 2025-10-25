// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
// Additional contributions by:                                               //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Compressed instruction decoder                             //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decodes RISC-V compressed instructions into their RV32     //
//                 equivalent. This module is fully combinatorial.            //
//                 Float extensions added                                     //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Module: cv32e40p_compressed_decoder
///////////////////////////////////////////////////////////////////////////////
// 
// FUNCTION:
//   Expands 16-bit RISC-V Compressed (RV32C) instructions into equivalent
//   32-bit RV32I instructions. Supports all C0, C1, and C2 compressed formats.
//   Optional support for compressed floating-point loads/stores (C.FLD, C.FSD,
//   C.FLW, C.FSW) when FPU is enabled.
//
// COMPRESSION OVERVIEW:
//   RV32C reduces code size by ~25-30% through:
//   - 16-bit encoding for most common instructions
//   - Implicit register operands (sp, zero, ra)
//   - Reduced register set (x8-x15 "prime" registers for some formats)
//   - Small immediate fields with specialized encoding
//
// INSTRUCTION FORMAT GROUPS:
//   C0 (instr_i[1:0] = 00): Stack-relative and memory ops
//     - C.ADDI4SPN: Add immediate scaled by 4 to SP
//     - C.LW/C.SW: Load/store word with compressed offset
//     - C.FLD/C.FSD, C.FLW/C.FSW: FP loads/stores (if FPU enabled)
//
//   C1 (instr_i[1:0] = 01): Control flow and immediate arithmetic
//     - C.ADDI, C.LI, C.LUI, C.ADDI16SP: Immediate operations
//     - C.SRLI, C.SRAI, C.ANDI: Shift and logic immediates
//     - C.SUB, C.XOR, C.OR, C.AND: Register-register ALU
//     - C.J, C.JAL, C.BEQZ, C.BNEZ: Jumps and branches
//
//   C2 (instr_i[1:0] = 10): Register moves and misc operations
//     - C.SLLI: Logical left shift immediate
//     - C.LWSP, C.SWSP: Load/store word from/to stack
//     - C.MV, C.ADD: Register move and add
//     - C.JR, C.JALR: Jump register and link
//     - C.EBREAK: Breakpoint
//
// REGISTER ENCODING:
//   "Prime" registers (C0/C1 formats): 
//     - 3-bit encoding: 000-111 maps to x8-x15 (s0-s1, a0-a5)
//     - Represented as: {2'b01, instr_i[9:7]} or {2'b01, instr_i[4:2]}
//   Full registers (C2 format):
//     - 5-bit encoding: direct mapping to x0-x31
//
// ILLEGAL INSTRUCTION DETECTION:
//   - Reserved opcodes or invalid bit patterns
//   - Zero immediate fields where non-zero required (C.ADDI4SPN, C.ADDI16SP)
//   - FP instructions when FPU disabled
//   - Reserved shift amounts (shamt[5] = 1 for RV32)
//
// TIMING CHARACTERISTICS:
//   - Pure combinational logic (zero latency)
//   - Critical path: 16-bit input → opcode decode → immediate reconstruction
//   - Typical delay: 2-3 gate levels for simple expansions
//   - Worst case: C.ADDI4SPN immediate reconstruction (~5 gate levels)
//
// PARAMETERS:
//   FPU   - Enable floating-point instruction expansion (1 = enabled)
//   ZFINX - FP in integer registers (1 = ZFINX mode, disables FP loads/stores)
//
// INTERFACE:
//   instr_i         - 32-bit input (only [15:0] used for compressed)
//   instr_o         - Expanded 32-bit instruction (RV32I format)
//   is_compressed_o - High when instr_i[1:0] != 2'b11 (16-bit instruction)
//   illegal_instr_o - High when compressed instruction is illegal/unsupported
//
// IMPLEMENTATION NOTES:
//   - Immediate fields are reconstructed by rearranging and sign-extending bits
//   - Register fields use compressed encoding (3-bit or 5-bit)
//   - Output opcode is always 32-bit RV32I format
//   - Decoder does NOT validate expanded instruction legality (main decoder's job)
//
///////////////////////////////////////////////////////////////////////////////

module cv32e40p_compressed_decoder #(
    // FPU: Enable floating-point load/store instruction expansion
    // When 1, C.FLD/C.FSD (double) and C.FLW/C.FSW (single) are supported
    // When 0, these encodings trigger illegal_instr_o
    parameter FPU   = 0,
    
    // ZFINX: Floating-point in integer registers mode
    // When 1, FP operations use integer register file (no separate FP regs)
    // In ZFINX mode, FP load/store instructions are illegal (use integer loads)
    // Must be 0 when FPU=1 for standard F/D extensions
    parameter ZFINX = 0
) (
    // Input instruction (32-bit, but only [15:0] examined for compressed)
    // If instr_i[1:0] == 2'b11, instruction is not compressed (32-bit)
    // If instr_i[1:0] != 2'b11, instruction is compressed (16-bit RV32C)
    input  logic [31:0] instr_i,
    
    // Expanded 32-bit instruction output (RV32I format)
    // Always 32-bit, even when input is compressed
    // Valid when is_compressed_o is high
    output logic [31:0] instr_o,
    
    // Compressed instruction indicator
    // High: Input is 16-bit compressed (instr_i[1:0] != 2'b11)
    // Low:  Input is 32-bit standard (instr_i[1:0] == 2'b11)
    output logic        is_compressed_o,
    
    // Illegal compressed instruction flag
    // High: Compressed instruction encoding is reserved/illegal
    // Low:  Valid compressed instruction (or not compressed)
    // Main decoder will perform further legality checks on instr_o
    output logic        illegal_instr_o
);

  import cv32e40p_pkg::*;

  ///////////////////////////////////////////////////////////////////////////////
  // Compressed Instruction Decoder
  ///////////////////////////////////////////////////////////////////////////////
  // Pure combinational logic expands 16-bit RV32C to 32-bit RV32I
  // Decoding is organized by quadrant (instr_i[1:0]) and funct3 (instr_i[15:13])

  //////////////////////////////////////////////////////////////////////////////////////////////////////
  //   ____                                                 _   ____                     _            //
  //  / ___|___  _ __ ___  _ __  _ __ ___  ___ ___  ___  __| | |  _ \  ___  ___ ___   __| | ___ _ __  //
  // | |   / _ \| '_ ` _ \| '_ \| '__/ _ \/ __/ __|/ _ \/ _` | | | | |/ _ \/ __/ _ \ / _` |/ _ \ '__| //
  // | |__| (_) | | | | | | |_) | | |  __/\__ \__ \  __/ (_| | | |_| |  __/ (_| (_) | (_| |  __/ |    //
  //  \____\___/|_| |_| |_| .__/|_|  \___||___/___/\___|\__,_| |____/ \___|\___\___/ \__,_|\___|_|    //
  //                      |_|                                                                         //
  //////////////////////////////////////////////////////////////////////////////////////////////////////

  always_comb begin
    // Default outputs: no illegal instruction, zero output
    illegal_instr_o = 1'b0;
    instr_o         = '0;

    ///////////////////////////////////////////////////////////////////////////////
    // Quadrant Decoding (instr_i[1:0])
    ///////////////////////////////////////////////////////////////////////////////
    // RV32C uses bits [1:0] to identify instruction format quadrant:
    //   00 (C0): Wide immediate ops, stack ops, memory ops
    //   01 (C1): Control transfer and ALU immediate/register ops  
    //   10 (C2): Stack loads/stores, register moves, system ops
    //   11: NOT compressed (standard 32-bit instruction, pass through)
    
    unique case (instr_i[1:0])
      ///////////////////////////////////////////////////////////////////////////
      // QUADRANT C0: Stack-Pointer and Memory Operations (instr_i[1:0] = 00)
      ///////////////////////////////////////////////////////////////////////////
      // Instructions in this quadrant typically involve stack manipulation
      // and memory accesses with compressed offsets
      
      // C0
      2'b00: begin
        unique case (instr_i[15:13])
          //---------------------------------------------------------------------
          // C.ADDI4SPN: Add Immediate Scaled by 4 to Stack Pointer
          //---------------------------------------------------------------------
          // Format: CI (compressed immediate)
          // Expands to: ADDI rd', x2, nzuimm
          // Encoding: 000 | nzuimm[5:4,9:6,2,3] | rd' | 00
          // Purpose: Allocate stack frame or compute stack-relative address
          // Immediate: Zero-extended 10-bit unsigned (nzuimm[9:2]), scaled by 4
          //           Final range: 4 to 1020 bytes
          // Destination: rd' = x8-x15 (compressed register encoding)
          // Special: nzuimm = 0 is illegal (reserved encoding)
          
          3'b000: begin
            // c.addi4spn -> addi rd', x2, imm
            instr_o = {
              2'b0,              // imm[11:10] = 00 (zero-extend)
              instr_i[10:7],     // imm[9:6]   from bits [10:7]
              instr_i[12:11],    // imm[5:4]   from bits [12:11]
              instr_i[5],        // imm[3]     from bit [5]
              instr_i[6],        // imm[2]     from bit [6]
              2'b00,             // imm[1:0]   = 00 (implicit scale by 4)
              5'h02,             // rs1 = x2 (stack pointer)
              3'b000,            // funct3 = ADDI
              2'b01,             // rd[4:3] = 01 (compressed register base)
              instr_i[4:2],      // rd[2:0]    from bits [4:2]
              OPCODE_OPIMM       // I-type ALU operation
            };
            // Illegal if immediate is zero (no useful operation)
            if (instr_i[12:5] == 8'b0) illegal_instr_o = 1'b1;
          end

          //---------------------------------------------------------------------
          // C.FLD: Floating-Point Load Double (64-bit)
          //---------------------------------------------------------------------
          // Format: CL (compressed load)
          // Expands to: FLD rd', offset(rs1')
          // Encoding: 001 | uimm[5:3] | rs1' | uimm[7:6] | rd' | 00
          // Purpose: Load 64-bit FP value from memory
          // Offset: Unsigned 8-bit, scaled by 8 (uimm[7:3], final range: 0-248)
          // Only valid when FPU=1 and ZFINX=0 (standard F/D extension)
          // ZFINX uses integer loads instead
          
          3'b001: begin
            // c.fld -> fld rd', imm(rs1')
            if (FPU == 1 && ZFINX == 0)
              // instr_i[12:10]-> offset[5:3],  instr_i[6:5]-> offset[7:6]
              instr_o = {
                4'b0,              // imm[11:8] = 0000 (zero-extend)
                instr_i[6:5],      // imm[7:6]  from bits [6:5]
                instr_i[12:10],    // imm[5:3]  from bits [12:10]
                3'b000,            // imm[2:0]  = 000 (implicit scale by 8)
                2'b01,             // rs1[4:3]  = 01 (compressed register)
                instr_i[9:7],      // rs1[2:0]  from bits [9:7]
                3'b011,            // funct3 = FLD (double-precision load)
                2'b01,             // rd[4:3]   = 01 (compressed register)
                instr_i[4:2],      // rd[2:0]   from bits [4:2]
                OPCODE_LOAD_FP     // FP load opcode
              };
            else illegal_instr_o = 1'b1;  // Illegal if FPU disabled or ZFINX mode
          end

          //---------------------------------------------------------------------
          // C.LW: Load Word (32-bit)
          //---------------------------------------------------------------------
          // Format: CL (compressed load)
          // Expands to: LW rd', offset(rs1')
          // Encoding: 010 | uimm[5:3] | rs1' | uimm[2,6] | rd' | 00
          // Purpose: Load 32-bit integer value from memory
          // Offset: Unsigned 7-bit, scaled by 4 (uimm[6:2], final range: 0-124)
          
          3'b010: begin
            // c.lw -> lw rd', imm(rs1')
            instr_o = {
              5'b0,              // imm[11:7] = 00000 (zero-extend)
              instr_i[5],        // imm[6]    from bit [5]
              instr_i[12:10],    // imm[5:3]  from bits [12:10]
              instr_i[6],        // imm[2]    from bit [6]
            instr_o = {
              5'b0,              // imm[11:7] = 00000 (zero-extend)
              instr_i[5],        // imm[6]    from bit [5]
              instr_i[12:10],    // imm[5:3]  from bits [12:10]
              instr_i[6],        // imm[2]    from bit [6]
              2'b00,             // imm[1:0]  = 00 (implicit scale by 4)
              2'b01,             // rs1[4:3]  = 01 (compressed register)
              instr_i[9:7],      // rs1[2:0]  from bits [9:7]
              3'b010,            // funct3 = LW (word load)
              2'b01,             // rd[4:3]   = 01 (compressed register)
              instr_i[4:2],      // rd[2:0]   from bits [4:2]
              OPCODE_LOAD        // Integer load opcode
            };
          end

          //---------------------------------------------------------------------
          // C.FLW: Floating-Point Load Word (32-bit)
          //---------------------------------------------------------------------
          // Format: CL (compressed load)
          // Expands to: FLW rd', offset(rs1')
          // Encoding: 011 | uimm[5:3] | rs1' | uimm[2,6] | rd' | 00
          // Purpose: Load 32-bit FP value (single-precision) from memory
          // Offset: Same as C.LW (unsigned 7-bit, scaled by 4)
          // Only valid when FPU=1 and ZFINX=0
          
          3'b011: begin
            // c.flw -> flw rd', imm(rs1')
            if (FPU == 1 && ZFINX == 0)
              instr_o = {
                5'b0,              // imm[11:7] = 00000 (zero-extend)
                instr_i[5],        // imm[6]    from bit [5]
                instr_i[12:10],    // imm[5:3]  from bits [12:10]
                instr_i[6],        // imm[2]    from bit [6]
                2'b00,             // imm[1:0]  = 00 (implicit scale by 4)
                2'b01,             // rs1[4:3]  = 01 (compressed register)
                instr_i[9:7],      // rs1[2:0]  from bits [9:7]
                3'b010,            // funct3 = FLW (single-precision load)
                2'b01,             // rd[4:3]   = 01 (compressed register)
                instr_i[4:2],      // rd[2:0]   from bits [4:2]
                OPCODE_LOAD_FP     // FP load opcode
              };
            else illegal_instr_o = 1'b1;  // Illegal if FPU disabled or ZFINX
          end

          //---------------------------------------------------------------------
          // C.FSD: Floating-Point Store Double (64-bit)
          //---------------------------------------------------------------------
          // Format: CS (compressed store)
          // Expands to: FSD rs2', offset(rs1')
          // Encoding: 101 | uimm[5:3] | rs1' | uimm[7:6] | rs2' | 00
          // Purpose: Store 64-bit FP value to memory
          // Offset: Unsigned 8-bit, scaled by 8 (uimm[7:3], range: 0-248)
          // Only valid when FPU=1 and ZFINX=0
          
          3'b101: begin
            // c.fsd -> fsd rs2', imm(rs1')
            if (FPU == 1 && ZFINX == 0)
              // instr_i[12:10] -> offset[5:3], instr_i[6:5] -> offset[7:6]
              instr_o = {
                4'b0,              // imm[11:8] = 0000 (zero-extend)
                instr_i[6:5],      // imm[7:6]  from bits [6:5]
                instr_i[12],       // imm[5]    from bit [12]
                2'b01,             // rs2[4:3]  = 01 (compressed register)
                instr_i[4:2],      // rs2[2:0]  from bits [4:2]
                2'b01,             // rs1[4:3]  = 01 (compressed register)
                instr_i[9:7],      // rs1[2:0]  from bits [9:7]
                3'b011,            // funct3 = FSD (double-precision store)
                instr_i[11:10],    // imm[4:3]  from bits [11:10]
                3'b000,            // imm[2:0]  = 000 (implicit scale by 8)
                OPCODE_STORE_FP    // FP store opcode
              };
            else illegal_instr_o = 1'b1;  // Illegal if FPU disabled or ZFINX
          end

          //---------------------------------------------------------------------
          // C.SW: Store Word (32-bit)
          //---------------------------------------------------------------------
          // Format: CS (compressed store)
          // Expands to: SW rs2', offset(rs1')
          // Encoding: 110 | uimm[5:3] | rs1' | uimm[2,6] | rs2' | 00
          // Purpose: Store 32-bit integer value to memory
          // Offset: Unsigned 7-bit, scaled by 4 (uimm[6:2], range: 0-124)
          
          3'b110: begin
            // c.sw -> sw rs2', imm(rs1')
            instr_o = {
              5'b0,              // imm[11:7] = 00000 (zero-extend)
              instr_i[5],        // imm[6]    from bit [5]
              instr_i[12],       // imm[5]    from bit [12]
              2'b01,             // rs2[4:3]  = 01 (compressed register)
              instr_i[4:2],      // rs2[2:0]  from bits [4:2]
              2'b01,             // rs1[4:3]  = 01 (compressed register)
              instr_i[9:7],      // rs1[2:0]  from bits [9:7]
              3'b010,            // funct3 = SW (word store)
              instr_i[11:10],    // imm[4:3]  from bits [11:10]
              instr_i[6],        // imm[2]    from bit [6]
              2'b00,             // imm[1:0]  = 00 (implicit scale by 4)
              OPCODE_STORE       // Integer store opcode
            };
          end

          //---------------------------------------------------------------------
          // C.FSW: Floating-Point Store Word (32-bit)
          //---------------------------------------------------------------------
          // Format: CS (compressed store)
          // Expands to: FSW rs2', offset(rs1')
          // Encoding: 111 | uimm[5:3] | rs1' | uimm[2,6] | rs2' | 00
          // Purpose: Store 32-bit FP value (single-precision) to memory
          // Offset: Same as C.SW (unsigned 7-bit, scaled by 4)
          // Only valid when FPU=1 and ZFINX=0
          
          3'b111: begin
            // c.fsw -> fsw rs2', imm(rs1')
            if (FPU == 1 && ZFINX == 0)
              instr_o = {
                5'b0,              // imm[11:7] = 00000 (zero-extend)
                instr_i[5],        // imm[6]    from bit [5]
                instr_i[12],       // imm[5]    from bit [12]
                2'b01,             // rs2[4:3]  = 01 (compressed register)
                instr_i[4:2],      // rs2[2:0]  from bits [4:2]
                2'b01,             // rs1[4:3]  = 01 (compressed register)
                instr_i[9:7],      // rs1[2:0]  from bits [9:7]
                3'b010,            // funct3 = FSW (single-precision store)
                instr_i[11:10],    // imm[4:3]  from bits [11:10]
                instr_i[6],        // imm[2]    from bit [6]
                2'b00,             // imm[1:0]  = 00 (implicit scale by 4)
                OPCODE_STORE_FP    // FP store opcode
              };
            else illegal_instr_o = 1'b1;  // Illegal if FPU disabled or ZFINX
          end
          
          default: begin
            illegal_instr_o = 1'b1;  // Reserved C0 encoding
          end
        endcase
      end


      ///////////////////////////////////////////////////////////////////////////
      // QUADRANT C1: Control Flow and ALU Operations (instr_i[1:0] = 01)
      ///////////////////////////////////////////////////////////////////////////
      // Instructions for jumps, branches, and immediate arithmetic/logic
      // Also includes register-register ALU operations
      
      // C1
      2'b01: begin
        unique case (instr_i[15:13])
          //---------------------------------------------------------------------
          // C.ADDI / C.NOP: Add Immediate
          //---------------------------------------------------------------------
          // Format: CI (compressed immediate)
          // Expands to: ADDI rd, rd, nzimm
          // Encoding: 000 | nzimm[5] | rd | nzimm[4:0] | 01
          // Purpose: Add sign-extended 6-bit immediate to register
          // Special case: C.NOP when rd=x0 and imm=0 (hint when rd=x0)
          // Immediate: Sign-extended 6-bit (nzimm[5:0], range: -32 to 31)
          
          3'b000: begin
            // c.addi -> addi rd, rd, nzimm
            // c.nop
            instr_o = {
              {6{instr_i[12]}},  // imm[11:6] = sign-extend from bit [12]
              instr_i[12],       // imm[5]    from bit [12]
              instr_i[6:2],      // imm[4:0]  from bits [6:2]
              instr_i[11:7],     // rs1 = rd  (source and dest are same)
              3'b0,              // funct3 = ADDI
              instr_i[11:7],     // rd        from bits [11:7]
              OPCODE_OPIMM       // I-type ALU immediate
            };
          end

          //---------------------------------------------------------------------
          // C.JAL (RV32) / C.J: Jump and Link / Jump
          //---------------------------------------------------------------------
          // Format: CJ (compressed jump)
          // C.JAL (funct3=001): Expands to JAL x1, offset  (call subroutine)
          // C.J   (funct3=101): Expands to JAL x0, offset  (unconditional jump)
          // Encoding: funct3 | offset[11,4,9:8,10,6,7,3:1,5] | 01
          // Purpose: Unconditional relative jump
          // Offset: Sign-extended 12-bit (offset[11:1], range: ±2KB, aligned to 2)
          // Note: RV64 uses funct3=001 for C.ADDIW instead
          
          3'b001, 3'b101: begin
            // 001: c.jal -> jal x1, imm
            // 101: c.j   -> jal x0, imm
            instr_o = {
              instr_i[12],       // imm[20]   = sign bit
              instr_i[8],        // imm[10]   from bit [8]
              instr_i[10:9],     // imm[9:8]  from bits [10:9]
              instr_i[6],        // imm[7]    from bit [6]
              instr_i[7],        // imm[6]    from bit [7]
              instr_i[2],        // imm[5]    from bit [2]
              instr_i[11],       // imm[4]    from bit [11]
              instr_i[5:3],      // imm[3:1]  from bits [5:3]
              {9{instr_i[12]}},  // imm[19:11] = sign-extend
              4'b0,              // imm[10:7]  (overlap, sign-extended above)
              ~instr_i[15],      // rd = x1 if funct3=001, x0 if funct3=101
              OPCODE_JAL         // J-type jump and link
            };
          end

          //---------------------------------------------------------------------
          // C.LI: Load Immediate
          //---------------------------------------------------------------------
          // Format: CI (compressed immediate)
          // Expands to: ADDI rd, x0, imm
          // Encoding: 010 | imm[5] | rd | imm[4:0] | 01
          // Purpose: Load small immediate into register (equivalent to li pseudo-op)
          // Immediate: Sign-extended 6-bit (imm[5:0], range: -32 to 31)
          // Special: rd=x0 is a hint (legal but discarded)
          
          3'b010: begin
            if (instr_i[11:7] == 5'b0) begin
              // Hint -> addi x0, x0, nzimm
              instr_o = {
                {6{instr_i[12]}}, instr_i[12], instr_i[6:2], 5'b0, 3'b0, instr_i[11:7], OPCODE_OPIMM
              };
            end else begin
              // c.li -> addi rd, x0, nzimm
              instr_o = {
                {6{instr_i[12]}}, instr_i[12], instr_i[6:2], 5'b0, 3'b0, instr_i[11:7], OPCODE_OPIMM
              };
            end
          end

          3'b011: begin
            if ({instr_i[12], instr_i[6:2]} == 6'b0) begin
              illegal_instr_o = 1'b1;
            end else begin
              if (instr_i[11:7] == 5'h02) begin
                // c.addi16sp -> addi x2, x2, nzimm
                instr_o = {
                  {3{instr_i[12]}},
                  instr_i[4:3],
                  instr_i[5],
                  instr_i[2],
                  instr_i[6],
                  4'b0,
                  5'h02,
                  3'b000,
                  5'h02,
                  OPCODE_OPIMM
                };
              end else if (instr_i[11:7] == 5'b0) begin
                // Hint -> lui x0, imm
                instr_o = {{15{instr_i[12]}}, instr_i[6:2], instr_i[11:7], OPCODE_LUI};
              end else begin
                // c.lui -> lui rd, imm
                instr_o = {{15{instr_i[12]}}, instr_i[6:2], instr_i[11:7], OPCODE_LUI};
              end
            end
          end

          3'b100: begin
            unique case (instr_i[11:10])
              2'b00, 2'b01: begin
                // 00: c.srli -> srli rd, rd, shamt
                // 01: c.srai -> srai rd, rd, shamt
                if (instr_i[12] == 1'b1) begin
                  // Reserved for future custom extensions (instr_o don't care)
                  instr_o = {
                    1'b0,
                    instr_i[10],
                    5'b0,
                    instr_i[6:2],
                    2'b01,
                    instr_i[9:7],
                    3'b101,
                    2'b01,
                    instr_i[9:7],
                    OPCODE_OPIMM
                  };
                  illegal_instr_o = 1'b1;
                end else begin
                  if (instr_i[6:2] == 5'b0) begin
                    // Hint
                    instr_o = {
                      1'b0,
                      instr_i[10],
                      5'b0,
                      instr_i[6:2],
                      2'b01,
                      instr_i[9:7],
                      3'b101,
                      2'b01,
                      instr_i[9:7],
                      OPCODE_OPIMM
                    };
                  end else begin
                    instr_o = {
                      1'b0,
                      instr_i[10],
                      5'b0,
                      instr_i[6:2],
                      2'b01,
                      instr_i[9:7],
                      3'b101,
                      2'b01,
                      instr_i[9:7],
                      OPCODE_OPIMM
                    };
                  end
                end
              end

              2'b10: begin
                // c.andi -> andi rd, rd, imm
                instr_o = {
                  {6{instr_i[12]}},
                  instr_i[12],
                  instr_i[6:2],
                  2'b01,
                  instr_i[9:7],
                  3'b111,
                  2'b01,
                  instr_i[9:7],
                  OPCODE_OPIMM
                };
              end

              2'b11: begin
                unique case ({
                  instr_i[12], instr_i[6:5]
                })
                  3'b000: begin
                    // c.sub -> sub rd', rd', rs2'
                    instr_o = {
                      2'b01,
                      5'b0,
                      2'b01,
                      instr_i[4:2],
                      2'b01,
                      instr_i[9:7],
                      3'b000,
                      2'b01,
                      instr_i[9:7],
                      OPCODE_OP
                    };
                  end

                  3'b001: begin
                    // c.xor -> xor rd', rd', rs2'
                    instr_o = {
                      7'b0,
                      2'b01,
                      instr_i[4:2],
                      2'b01,
                      instr_i[9:7],
                      3'b100,
                      2'b01,
                      instr_i[9:7],
                      OPCODE_OP
                    };
                  end

                  3'b010: begin
                    // c.or  -> or  rd', rd', rs2'
                    instr_o = {
                      7'b0,
                      2'b01,
                      instr_i[4:2],
                      2'b01,
                      instr_i[9:7],
                      3'b110,
                      2'b01,
                      instr_i[9:7],
                      OPCODE_OP
                    };
                  end

                  3'b011: begin
                    // c.and -> and rd', rd', rs2'
                    instr_o = {
                      7'b0,
                      2'b01,
                      instr_i[4:2],
                      2'b01,
                      instr_i[9:7],
                      3'b111,
                      2'b01,
                      instr_i[9:7],
                      OPCODE_OP
                    };
                  end

                  3'b100, 3'b101, 3'b110, 3'b111: begin
                    // 100: c.subw
                    // 101: c.addw
                    illegal_instr_o = 1'b1;
                  end
                endcase
              end
            endcase
          end

          3'b110, 3'b111: begin
            // 0: c.beqz -> beq rs1', x0, imm
            // 1: c.bnez -> bne rs1', x0, imm
            instr_o = {
              {4{instr_i[12]}},
              instr_i[6:5],
              instr_i[2],
              5'b0,
              2'b01,
              instr_i[9:7],
              2'b00,
              instr_i[13],
              instr_i[11:10],
              instr_i[4:3],
              instr_i[12],
              OPCODE_BRANCH
            };
          end
        endcase
      end

      // C2
      2'b10: begin
        unique case (instr_i[15:13])
          3'b000: begin
            if (instr_i[12] == 1'b1) begin
              // Reserved for future extensions (instr_o don't care)
              instr_o = {7'b0, instr_i[6:2], instr_i[11:7], 3'b001, instr_i[11:7], OPCODE_OPIMM};
              illegal_instr_o = 1'b1;
            end else begin
              if ((instr_i[6:2] == 5'b0) || (instr_i[11:7] == 5'b0)) begin
                // Hint -> slli rd, rd, shamt 
                instr_o = {7'b0, instr_i[6:2], instr_i[11:7], 3'b001, instr_i[11:7], OPCODE_OPIMM};
              end else begin
                // c.slli -> slli rd, rd, shamt
                instr_o = {7'b0, instr_i[6:2], instr_i[11:7], 3'b001, instr_i[11:7], OPCODE_OPIMM};
              end
            end
          end

          3'b001: begin
            // c.fldsp -> fld rd, imm(x2)
            if (FPU == 1 && ZFINX == 0)
              // instr_i[6:5] -> offset[4:3], instr_i[4:2] -> offset[8:6], instr_i[12] -> offset[5]
              instr_o = {
                3'b0,
                instr_i[4:2],
                instr_i[12],
                instr_i[6:5],
                3'b000,
                5'h02,
                3'b011,
                instr_i[11:7],
                OPCODE_LOAD_FP
              };
            else illegal_instr_o = 1'b1;
          end

          3'b010: begin
            // c.lwsp -> lw rd, imm(x2)
            instr_o = {
              4'b0,
              instr_i[3:2],
              instr_i[12],
              instr_i[6:4],
              2'b00,
              5'h02,
              3'b010,
              instr_i[11:7],
              OPCODE_LOAD
            };
            if (instr_i[11:7] == 5'b0) illegal_instr_o = 1'b1;
          end

          3'b011: begin
            // c.flwsp -> flw rd, imm(x2)
            if (FPU == 1 && ZFINX == 0)
              instr_o = {
                4'b0,
                instr_i[3:2],
                instr_i[12],
                instr_i[6:4],
                2'b00,
                5'h02,
                3'b010,
                instr_i[11:7],
                OPCODE_LOAD_FP
              };
            else illegal_instr_o = 1'b1;
          end

          3'b100: begin
            if (instr_i[12] == 1'b0) begin
              if (instr_i[6:2] == 5'b0) begin
                // c.jr -> jalr x0, rd/rs1, 0
                instr_o = {12'b0, instr_i[11:7], 3'b0, 5'b0, OPCODE_JALR};
                // c.jr with rs1 = 0 is reserved
                if (instr_i[11:7] == 5'b0) illegal_instr_o = 1'b1;
              end else begin
                if (instr_i[11:7] == 5'b0) begin
                  // Hint -> add x0, x0, rs2
                  instr_o = {7'b0, instr_i[6:2], 5'b0, 3'b0, instr_i[11:7], OPCODE_OP};
                end else begin
                  // c.mv -> add rd, x0, rs2
                  instr_o = {7'b0, instr_i[6:2], 5'b0, 3'b0, instr_i[11:7], OPCODE_OP};
                end
              end
            end else begin
              if (instr_i[6:2] == 5'b0) begin
                if (instr_i[11:7] == 5'b0) begin
                  // c.ebreak -> ebreak
                  instr_o = {32'h00_10_00_73};
                end else begin
                  // c.jalr -> jalr x1, rs1, 0
                  instr_o = {12'b0, instr_i[11:7], 3'b000, 5'b00001, OPCODE_JALR};
                end
              end else begin
                if (instr_i[11:7] == 5'b0) begin
                  // Hint -> add x0, x0, rs2
                  instr_o = {7'b0, instr_i[6:2], instr_i[11:7], 3'b0, instr_i[11:7], OPCODE_OP};
                end else begin
                  // c.add -> add rd, rd, rs2
                  instr_o = {7'b0, instr_i[6:2], instr_i[11:7], 3'b0, instr_i[11:7], OPCODE_OP};
                end
              end
            end
          end

          3'b101: begin
            // c.fsdsp -> fsd rs2, imm(x2)
            if (FPU == 1 && ZFINX == 0)
              // instr_i[12:10] -> offset[5:3], instr_i[9:7] -> offset[8:6]
              instr_o = {
                3'b0,
                instr_i[9:7],
                instr_i[12],
                instr_i[6:2],
                5'h02,
                3'b011,
                instr_i[11:10],
                3'b000,
                OPCODE_STORE_FP
              };
            else illegal_instr_o = 1'b1;
          end
          3'b110: begin
            // c.swsp -> sw rs2, imm(x2)
            instr_o = {
              4'b0,
              instr_i[8:7],
              instr_i[12],
              instr_i[6:2],
              5'h02,
              3'b010,
              instr_i[11:9],
              2'b00,
              OPCODE_STORE
            };
          end

          3'b111: begin
            // c.fswsp -> fsw rs2, imm(x2)
            if (FPU == 1 && ZFINX == 0)
              instr_o = {
                4'b0,
                instr_i[8:7],
                instr_i[12],
                instr_i[6:2],
                5'h02,
                3'b010,
                instr_i[11:9],
                2'b00,
                OPCODE_STORE_FP
              };
            else illegal_instr_o = 1'b1;
          end
        endcase
      end

      //-----------------------------------------------------------------------
      // DEFAULT: 32-bit Standard Instructions (instr_i[1:0] = 11)
      //-----------------------------------------------------------------------
      // When bits [1:0] = 11, instruction is not compressed (standard RV32I)
      // Pass through unchanged - no expansion needed
      
      default: begin
        // 32 bit (or more) instruction
        instr_o = instr_i;
      end
    endcase
  end

  ///////////////////////////////////////////////////////////////////////////////
  // Compressed Instruction Detection
  ///////////////////////////////////////////////////////////////////////////////
  // Standard RISC-V encoding: bits [1:0] determine instruction length
  //   00, 01, 10: 16-bit compressed instruction (RV32C)
  //   11:         32-bit standard instruction (RV32I/M/A/F/D)
  // This signal tells IF/ID stage whether to consume 16 or 32 bits from buffer
  
  assign is_compressed_o = (instr_i[1:0] != 2'b11);

  ///////////////////////////////////////////////////////////////////////////////
  // Implementation Notes and Alternatives
  ///////////////////////////////////////////////////////////////////////////////
  // IMMEDIATE ENCODING COMPLEXITY:
  // Compressed immediates use non-contiguous bit fields to maximize encoding
  // efficiency. Each instruction type shuffles bits differently:
  //   - C.ADDI4SPN: nzuimm[9:2] scattered across [12:5] (zero-extended)
  //   - C.JAL/C.J:  simm[11:1] with irregular ordering (sign-extended)
  //   - C.ADDI16SP: nzimm[9:4] in special arrangement (sign-extended)
  //   - C.LW/C.SW:  uimm[6:2] with non-sequential bit positions
  // 
  // ALTERNATIVE IMPLEMENTATION: Table-Driven Decoder
  // For very large RV32C implementations or verification:
  //   - Create lookup table mapping 16-bit → 32-bit (64K entries)
  //   - Trade logic complexity for memory (16KB ROM)
  //   - Faster simulation, easier verification
  //   - Not practical for synthesis (too large)
  //
  // ALTERNATIVE IMPLEMENTATION: Microcode Expansion
  // For complex processors with already-microcoded control:
  //   - Expand compressed instructions into micro-ops directly
  //   - Skip intermediate 32-bit RV32I representation
  //   - Saves decode logic but increases microcode ROM size
  //   - Used in some out-of-order implementations
  //
  // CRITICAL PATH ANALYSIS:
  // Longest combinational paths:
  //   1. C.ADDI4SPN immediate reconstruction (8 input bits → 10-bit immediate)
  //      Path: instr_i[12:2] → bit rearrangement → instr_o[31:20]
  //      Delay: ~5 LUT levels (bit shuffling + zero-extension)
  //
  //   2. C.JAL/C.J immediate reconstruction (11 input bits → 20-bit immediate)
  //      Path: instr_i[12:2] → complex rearrangement + sign-extend → instr_o[31:12]
  //      Delay: ~6 LUT levels (scattered bits + sign extension tree)
  //
  //   3. FPU check and illegal instruction logic
  //      Path: FPU parameter + instr_i[15:13] → illegal_instr_o
  //      Delay: ~2 LUT levels (AND/OR gates)
  //
  // OPTIMIZATION: Pipeline Compressed Decoder
  // For very high frequency designs (Fmax > 2 GHz):
  //   - Add register stage between compressed decoder and main decoder
  //   - Breaks critical path from IF to ID stage
  //   - Cost: +1 cycle latency for compressed instructions
  //   - Benefit: Higher Fmax for entire processor
  //
  // VERIFICATION CHALLENGES:
  // - Total RV32C instructions: ~40 different instruction types
  // - Each with multiple immediate/register combinations
  // - Formal verification recommended:
  //     * Assert instr_o legality for all compressed encodings
  //     * Equivalence check: compressed execution = expanded execution
  // - Use RISC-V ISA tests (riscv-tests/isa/rv32uc-*)
  //
  // HINT INSTRUCTIONS:
  // RV32C spec defines "hint" encodings (NOP-like operations):
  //   - C.ADDI with rd=x0: Hint (not illegal, just ignored)
  //   - C.LI with rd=x0: Hint
  //   - C.LUI with rd=x0: Hint
  //   - C.SRLI/C.SRAI with shamt=0: Hint (RV64 uses shamt[5])
  // These are expanded to legal instructions that write to x0
  // Main decoder should handle writes to x0 correctly (discard result)
  //
  // FPGA IMPLEMENTATION:
  // Synthesis tools typically map immediate reconstruction to LUTs
  //   - Xilinx: 6-input LUTs can handle 2-3 bit shuffle stages
  //   - Intel: ALMs can implement complex bit rearrangements efficiently
  //   - Expect ~50-100 LUTs for complete decoder
  // Resource sharing opportunities:
  //   - Many instructions share similar immediate patterns (C.LW/C.SW, C.FLW/C.FSW)
  //   - Synthesizer will merge common logic

endmodule
