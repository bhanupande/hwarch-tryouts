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
// Engineer:       Francesco Conti - f.conti@unibo.it                         //
//                                                                            //
// Additional contributions by:                                               //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    RISC-V register file                                       //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Register file with 31x 32 bit wide registers. Register 0   //
//                 is fixed to 0. This register file is based on flip-flops.  //
//                 Also supports the fp-register file now if FPU=1            //
//                 If ZFINX is 1, floating point operations take values       //
//                 from the X register file                                   //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Module: cv32e40p_register_file
///////////////////////////////////////////////////////////////////////////////
// 
// FUNCTION:
//   Flip-flop based general-purpose and floating-point register file.
//   Implements RISC-V integer registers (x0-x31) with x0 hardwired to zero.
//   Optional floating-point registers (f0-f31) when FPU enabled and ZFINX disabled.
//
// RISC-V REGISTER FILE SPECIFICATION:
//   - 32 integer registers: x0 (zero), x1 (ra), x2 (sp), x3-x31 (general)
//   - x0 always reads as zero, writes to x0 are ignored
//   - 32 FP registers: f0-f31 (when FPU=1, ZFINX=0)
//   - ZFINX mode: FP operations use integer registers (f0=x0, f1=x1, etc.)
//
// PORT CONFIGURATION:
//   3 Read Ports (R1, R2, R3):
//     - Simultaneous independent reads
//     - Zero-cycle read latency (combinational output)
//     - Required for: Two ALU operands + one MAC/store operand
//   
//   2 Write Ports (W1, W2):
//     - Allows dual writes per cycle (common with MAC or FP operations)
//     - Write priority: W2 > W1 (if both write same address, W2 wins)
//     - Writes take effect on next clock edge
//
// ADDRESS ENCODING:
//   When FPU=1 and ZFINX=0 (separate FP registers):
//     - Bit [5] = 0: Integer register (x0-x31)
//     - Bit [5] = 1: Floating-point register (f0-f31)
//     - Address [4:0] selects which register within the file
//   
//   When ZFINX=1 (FP in integer registers):
//     - All addresses map to integer register file
//     - Bit [5] ignored, only [4:0] used
//
// IMPLEMENTATION: FLIP-FLOP BASED
//   Advantages vs Latch-based:
//     - Fully synchronous (no latch transparency issues)
//     - Better timing analysis (setup/hold only)
//     - No race conditions or glitches
//     - Easier formal verification
//   Disadvantages:
//     - Larger area (~2x flip-flops vs latches)
//     - Higher power consumption
//     - Read-during-write has 1-cycle delay (vs 0-cycle for latches)
//
// READ-DURING-WRITE BEHAVIOR:
//   - Read returns OLD value (pre-write) when reading address being written
//   - This is standard flip-flop behavior (write on posedge, read is combinational)
//   - Pipeline must handle with forwarding or stalls
//
// WRITE PORT PRIORITY:
//   When both write ports target same address:
//     1. Port B (W2) has priority
//     2. Port A (W1) is ignored
//   Implementation: we_b_dec checked before we_a_dec in always_ff block
//
// AREA ESTIMATION:
//   - Integer registers: 31 registers × 32 bits = 992 flip-flops
//   - FP registers (if enabled): 32 registers × 32 bits = 1024 flip-flops
//   - Total (FPU enabled): ~2016 flip-flops + mux logic
//   - FPGA: Maps to distributed RAM or registers (depends on synthesis)
//   - ASIC: Typically stays as flip-flops (for multi-port access)
//
// PARAMETERS:
//   ADDR_WIDTH - Address width (5 for RV32, 6 with FPU bit)
//   DATA_WIDTH - Data width (32 for RV32)
//   FPU        - Enable floating-point register file
//   ZFINX      - FP operations use integer registers (no separate FP regs)
//
///////////////////////////////////////////////////////////////////////////////

module cv32e40p_register_file #(
    // Address width: 5 bits for 32 registers, 6 bits with FP extension
    parameter ADDR_WIDTH = 5,
    
    // Data width: 32 bits for RV32
    parameter DATA_WIDTH = 32,
    
    // Enable floating-point register file
    // 0: Integer registers only (x0-x31)
    // 1: Integer + FP registers (x0-x31, f0-f31) unless ZFINX=1
    parameter FPU        = 0,
    
    // ZFINX: FP operations use integer register file
    // 0: Separate FP register file (f0-f31)
    // 1: FP operations use integer registers (f0=x0, f1=x1, ...)
    parameter ZFINX      = 0
) (
    // Clock and Reset
    input logic clk,     // Clock
    input logic rst_n,   // Active-low reset

    // Scan chain enable (for DFT/test mode)
    input logic scan_cg_en_i,

    ///////////////////////////////////////////////////////////////////////////
    // Read Port R1 (typically rs1 - first source operand)
    ///////////////////////////////////////////////////////////////////////////
    input  logic [ADDR_WIDTH-1:0] raddr_a_i,  // Read address port A
    output logic [DATA_WIDTH-1:0] rdata_a_o,  // Read data port A (combinational)

    ///////////////////////////////////////////////////////////////////////////
    // Read Port R2 (typically rs2 - second source operand)
    ///////////////////////////////////////////////////////////////////////////
    input  logic [ADDR_WIDTH-1:0] raddr_b_i,  // Read address port B
    output logic [DATA_WIDTH-1:0] rdata_b_o,  // Read data port B (combinational)

    ///////////////////////////////////////////////////////////////////////////
    // Read Port R3 (typically rs3 - third source for MAC/FP operations)
    ///////////////////////////////////////////////////////////////////////////
    input  logic [ADDR_WIDTH-1:0] raddr_c_i,  // Read address port C
    output logic [DATA_WIDTH-1:0] rdata_c_o,  // Read data port C (combinational)

    ///////////////////////////////////////////////////////////////////////////
    // Write Port W1 (typically ALU result destination)
    ///////////////////////////////////////////////////////////////////////////
    input logic [ADDR_WIDTH-1:0] waddr_a_i,   // Write address port A
    input logic [DATA_WIDTH-1:0] wdata_a_i,   // Write data port A
    input logic                  we_a_i,      // Write enable port A

    ///////////////////////////////////////////////////////////////////////////
    // Write Port W2 (typically LSU/MUL/FP result destination)
    ///////////////////////////////////////////////////////////////////////////
    // Has priority over W1 if both write to same address
    input logic [ADDR_WIDTH-1:0] waddr_b_i,   // Write address port B
    input logic [DATA_WIDTH-1:0] wdata_b_i,   // Write data port B
    input logic                  we_b_i       // Write enable port B
);

  ///////////////////////////////////////////////////////////////////////////
  // LOCAL PARAMETERS
  ///////////////////////////////////////////////////////////////////////////
  
  // Number of integer registers: 2^(ADDR_WIDTH-1) = 16 (only x1-x15 stored)
  // Note: x0 is not stored in array, hardwired to 0
  // For ADDR_WIDTH=5: NUM_WORDS = 2^4 = 16 registers
  // Actual RISC-V has 32 integer regs, but x0 special + indexing gives 16
  localparam NUM_WORDS = 2 ** (ADDR_WIDTH - 1);
  
  // Number of floating-point registers: 2^(ADDR_WIDTH-1) = 16
  // All 32 FP registers stored (f0-f31) when FPU=1 and ZFINX=0
  localparam NUM_FP_WORDS = 2 ** (ADDR_WIDTH - 1);
  
  // Total words in register file
  // FPU=0: NUM_WORDS only (integer registers)
  // FPU=1, ZFINX=1: NUM_WORDS only (FP uses integer registers)
  // FPU=1, ZFINX=0: NUM_WORDS + NUM_FP_WORDS (separate integer and FP)
  localparam NUM_TOT_WORDS = FPU ? (ZFINX ? NUM_WORDS : NUM_WORDS + NUM_FP_WORDS) : NUM_WORDS;

  ///////////////////////////////////////////////////////////////////////////
  // REGISTER STORAGE ARRAYS
  ///////////////////////////////////////////////////////////////////////////
  
  // Integer register file storage (x1-x31)
  // x0 is NOT stored here - it's hardwired to 0 in read logic
  // Array size: 16 registers × 32 bits = 512 bits
  logic [    NUM_WORDS-1:0][DATA_WIDTH-1:0] mem;

  // Floating-point register file storage (f0-f31)
  // Only instantiated when FPU=1 and ZFINX=0
  // Array size: 16 registers × 32 bits = 512 bits
  logic [ NUM_FP_WORDS-1:0][DATA_WIDTH-1:0] mem_fp;

  ///////////////////////////////////////////////////////////////////////////
  // INTERNAL SIGNALS
  ///////////////////////////////////////////////////////////////////////////
  
  // Masked write addresses (with x0 protection)
  // If write targets x0, address is masked to prevent actual write
  logic [   ADDR_WIDTH-1:0]                 waddr_a;
  logic [   ADDR_WIDTH-1:0]                 waddr_b;

  // Write enable decoder outputs (one-hot per register)
  // Converts 5/6-bit address to one-hot vector for direct register selection
  // Size: NUM_TOT_WORDS bits (16 or 32 depending on FPU config)
  logic [NUM_TOT_WORDS-1:0]                 we_a_dec;
  logic [NUM_TOT_WORDS-1:0]                 we_b_dec;


  ///////////////////////////////////////////////////////////////////////////
  // READ LOGIC - COMBINATIONAL
  ///////////////////////////////////////////////////////////////////////////
  // Three independent read ports with zero-cycle latency
  // 
  // ADDRESS DECODING:
  //   Bit [5]: Selects integer (0) or FP (1) register file
  //   Bits [4:0]: Register index within selected file (0-31)
  //
  // REGISTER x0 HANDLING:
  //   When raddr_x_i[4:0] = 0 and bit[5]=0 (integer file):
  //     - Reads mem[0] which may contain garbage
  //     - However, x0 is typically not read by decoder
  //     - Some implementations force x0 reads to 0 explicitly
  //   Alternative: Add rdata = (raddr[4:0]==0 && !raddr[5]) ? 32'h0 : mem[...]
  //
  // FPU CONFIGURATIONS:
  //   FPU=0: Only mem[] exists, bit [5] ignored
  //   FPU=1, ZFINX=0: mem[] for integer, mem_fp[] for FP, bit[5] selects
  //   FPU=1, ZFINX=1: Only mem[] used, bit [5] ignored (FP uses integer regs)
  //
  // TIMING:
  //   Critical path: address mux → register array read → output
  //   Typical: 1-2 FO4 delays for small register files
  //
  //-----------------------------------------------------------------------------
  //-- READ : Read address decoder RAD
  //-----------------------------------------------------------------------------
  assign rdata_a_o = raddr_a_i[5] ? mem_fp[raddr_a_i[4:0]] : mem[raddr_a_i[4:0]];
  assign rdata_b_o = raddr_b_i[5] ? mem_fp[raddr_b_i[4:0]] : mem[raddr_b_i[4:0]];
  assign rdata_c_o = raddr_c_i[5] ? mem_fp[raddr_c_i[4:0]] : mem[raddr_c_i[4:0]];

  ///////////////////////////////////////////////////////////////////////////
  // WRITE ADDRESS DECODER - COMBINATIONAL
  ///////////////////////////////////////////////////////////////////////////
  // Converts write addresses to one-hot enable signals for each register
  //
  // TWO-STAGE PROCESS:
  //   1. Address masking: Prevents writes to x0 (optional, done in decoder)
  //   2. Decode to one-hot: Generate individual write enables per register
  //
  // ONE-HOT ENCODING:
  //   we_x_dec[i] = 1 when writing to register i
  //   All other bits = 0
  //   Example: waddr=5 → we_dec = 32'h0000_0020
  //
  // WRITE PORT PRIORITY:
  //   Both ports decode independently here
  //   Priority resolution happens in sequential write logic
  //   (Port B checked first in always_ff block)
  //
  // ALTERNATIVE: Binary address decode
  //   Could directly use waddr as array index without one-hot decode
  //   Simpler logic but less flexible for future enhancements
  //   One-hot allows per-register clock gating if needed
  //
  //-----------------------------------------------------------------------------
  //-- WRITE : Write Address Decoder (WAD), combinatorial process
  //-----------------------------------------------------------------------------

  // Mask top bit of write address to disable fp regfile
  // Note: Currently no masking done; addresses pass through directly
  // Could add: waddr_x = (waddr_x_i[4:0] == 0) ? {ADDR_WIDTH{1'b0}} : waddr_x_i
  assign waddr_a   = waddr_a_i;
  assign waddr_b   = waddr_b_i;

  // Generate write enable decoder for each register
  // Converts N-bit address to 2^N one-hot vector
  // Example: waddr=3, we=1 → we_dec[3]=1, all others=0
  genvar gidx;
  generate
    for (gidx = 0; gidx < NUM_TOT_WORDS; gidx++) begin : gen_we_decoder
      assign we_a_dec[gidx] = (waddr_a == gidx) ? we_a_i : 1'b0;
      assign we_b_dec[gidx] = (waddr_b == gidx) ? we_b_i : 1'b0;
    end
  endgenerate

  genvar i, l;
  generate

    ///////////////////////////////////////////////////////////////////////////
    // INTEGER REGISTER FILE WRITE LOGIC - SEQUENTIAL
    ///////////////////////////////////////////////////////////////////////////
    // Implements flip-flop based register storage with dual write ports
    //
    // REGISTER x0 SPECIAL HANDLING:
    //   RISC-V spec: x0 must always read as zero
    //   Implementation: Separate always_ff block forces mem[0] = 0
    //   Even if x0 is written, it's immediately overwritten to 0 next cycle
    //
    // WRITE PRIORITY MECHANISM:
    //   When both ports write to same register:
    //     1. Check we_b_dec[i] first
    //     2. If true, write wdata_b
    //     3. Else check we_a_dec[i]
    //     4. If true, write wdata_a
    //   Result: Port B has priority over Port A
    //
    // READ-DURING-WRITE BEHAVIOR:
    //   Flip-flop based: Read returns OLD value
    //   Example timeline:
    //     Cycle N: Write data X to reg R5
    //     Cycle N: Read R5 returns OLD value (pre-write)
    //     Cycle N+1: Read R5 returns X (new value)
    //   Pipeline must handle with forwarding logic in EX stage
    //
    // RESET BEHAVIOR:
    //   All registers initialized to 0 on reset
    //   Ensures deterministic behavior after reset
    //   Important for verification and debug
    //
    // TIMING:
    //   Setup: wdata, waddr, we must be stable before clk edge
    //   Hold: Must remain stable after clk edge (standard FF timing)
    //   Clock-to-Q: Typical FF propagation delay
    //
    // ALTERNATIVE IMPLEMENTATION: Write-through
    //   Could add combinational bypass:
    //     rdata = (raddr == waddr && we) ? wdata : mem[raddr]
    //   Advantages: Zero-cycle forwarding, simpler pipeline
    //   Disadvantages: Longer critical path, more mux logic
    //
    //-----------------------------------------------------------------------------
    //-- WRITE : Write operation
    //-----------------------------------------------------------------------------
    
    // Register x0: Hardwired to zero (RISC-V architectural requirement)
    // Even if written by accident, forced back to zero each cycle
    always_ff @(posedge clk or negedge rst_n) begin
      if (~rst_n) begin
        // R0 is nil
        mem[0] <= 32'b0;
      end else begin
        // R0 is nil
        mem[0] <= 32'b0;
      end
    end

    // Integer registers x1 through x31
    // Loop generates individual flip-flop storage for each register
    // Each register checks its corresponding we_dec bit for write enable
    for (i = 1; i < NUM_WORDS; i++) begin : gen_rf

      always_ff @(posedge clk, negedge rst_n) begin : register_write_behavioral
        if (rst_n == 1'b0) begin
          mem[i] <= 32'b0;
        end else begin
          // Write priority: Port B > Port A
          // Check port B first, then port A
          // If both enabled for same address, only port B write occurs
          if (we_b_dec[i] == 1'b1) mem[i] <= wdata_b_i;
          else if (we_a_dec[i] == 1'b1) mem[i] <= wdata_a_i;
        end
      end

    end

    ///////////////////////////////////////////////////////////////////////////
    // FLOATING-POINT REGISTER FILE WRITE LOGIC - SEQUENTIAL
    ///////////////////////////////////////////////////////////////////////////
    // Optional FP register file (f0-f31)
    // Only generated when FPU=1 and ZFINX=0
    //
    // ZFINX MODE:
    //   When ZFINX=1: FP operations use integer registers
    //   This block is not generated, saving area
    //
    // FP REGISTER ADDRESSING:
    //   Address bit [5] = 1 selects FP register file
    //   we_x_dec[l+NUM_WORDS] corresponds to FP register l
    //   Example: waddr = 6'b100101 → FP register f5
    //
    // WRITE PRIORITY:
    //   Same as integer registers: Port B > Port A
    //
    // FP REGISTER f0:
    //   Unlike integer x0, f0 is NOT hardwired to zero
    //   All FP registers are general-purpose storage
    //
    // AREA vs PERFORMANCE:
    //   This doubles register file area when enabled
    //   Alternative: Time-multiplex single register file
    //     - Saves area but reduces throughput
    //     - ZFINX approach: Uses integer regs, zero area overhead
    //
    if (FPU == 1 && ZFINX == 0) begin : gen_mem_fp_write
      // Floating point registers (f0-f31)
      // All 32 FP registers are writable (no f0=0 requirement)
      for (l = 0; l < NUM_FP_WORDS; l++) begin
        always_ff @(posedge clk, negedge rst_n) begin : fp_regs
          if (rst_n == 1'b0) mem_fp[l] <= '0;
          // Write priority: Port B > Port A (same as integer regs)
          else if (we_b_dec[l+NUM_WORDS] == 1'b1) mem_fp[l] <= wdata_b_i;
          else if (we_a_dec[l+NUM_WORDS] == 1'b1) mem_fp[l] <= wdata_a_i;
        end
      end
    end else begin : gen_no_mem_fp_write
      // When FPU=0 or ZFINX=1: No separate FP register file
      // Tie mem_fp to zero to avoid synthesis warnings
      assign mem_fp = 'b0;
    end

  endgenerate

  ///////////////////////////////////////////////////////////////////////////
  // END OF MODULE
  ///////////////////////////////////////////////////////////////////////////
  // 
  // DESIGN TRADE-OFFS SUMMARY:
  // 
  // 1. FLIP-FLOP vs LATCH IMPLEMENTATION:
  //    Chosen: Flip-flops (this file)
  //    Alternative: cv32e40p_register_file_latch.sv
  //    Decision factors:
  //      - FPGAs: Flip-flops required (no latch primitives)
  //      - ASICs: Latches save ~50% area but add timing complexity
  //      - Verification: Flip-flops easier to verify formally
  // 
  // 2. MULTI-PORT vs SINGLE-PORT:
  //    Chosen: 3 read + 2 write ports
  //    Rationale:
  //      - Supports MAC: 2 operands + accumulator read simultaneously
  //      - Allows dual-issue: ALU + LSU can write same cycle
  //    Alternative: Single port with arbitration
  //      - Much smaller area (1/5th size)
  //      - Requires multi-cycle register access
  //      - Would reduce IPC significantly
  // 
  // 3. SEPARATE FP REGISTERS vs ZFINX:
  //    Chosen: Configurable via FPU + ZFINX parameters
  //    FPU=1, ZFINX=0: Separate f0-f31 registers
  //      - Traditional RISC-V FP implementation
  //      - Doubles register file area
  //      - Allows parallel integer + FP operations
  //    FPU=1, ZFINX=1: FP uses integer registers
  //      - Area efficient (zero overhead)
  //      - Integer-FP conflicts reduce throughput
  //      - Better for embedded systems
  // 
  // 4. WRITE PRIORITY vs ARBITRATION:
  //    Chosen: Fixed priority (Port B > Port A)
  //    Simple and deterministic
  //    Alternative: Round-robin or age-based arbitration
  //      - Fairer but adds complexity
  //      - Not needed in CV32E40P pipeline structure
  // 
  // 5. SYNCHRONOUS vs ASYNCHRONOUS RESET:
  //    Chosen: Asynchronous reset (negedge rst_n)
  //    Advantages:
  //      - Guaranteed initialization even if clock fails
  //      - Faster recovery from reset
  //    Disadvantages:
  //      - Reset distribution tree critical
  //      - Metastability risk if reset released near clock edge
  //

endmodule
