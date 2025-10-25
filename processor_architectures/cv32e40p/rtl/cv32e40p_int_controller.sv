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
// Engineer:       Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
// Design Name:    Interrupt Controller                                       //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Interrupt Controller of the pipelined processor            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Module: cv32e40p_int_controller
///////////////////////////////////////////////////////////////////////////////
//
// FUNCTION:
//   Interrupt controller for CV32E40P RISC-V core.
//   Manages 32 external interrupt sources with priority encoding.
//   Interfaces between external interrupt signals and pipeline controller.
//
// RISC-V INTERRUPT ARCHITECTURE:
//   Standard RISC-V defines Machine-mode interrupts:
//     - MTI (bit 7): Machine Timer Interrupt
//     - MSI (bit 3): Machine Software Interrupt  
//     - MEI (bit 11): Machine External Interrupt
//   CV32E40P extends this with 16 fast custom interrupts (bits 16-31)
//
// INTERRUPT TYPES:
//   Standard (bits 0-15):
//     [11] MEI - Machine External Interrupt (highest standard priority)
//     [7]  MTI - Machine Timer Interrupt
//     [3]  MSI - Machine Software Interrupt
//     [0-2, 4-6, 8-10, 12-15] - Reserved (masked by IRQ_MASK)
//
//   Fast Custom (bits 16-31):
//     [31:16] - PULP fast interrupts (highest overall priority)
//     Designed for low-latency interrupt response
//     Common uses: DMA completion, peripheral events, accelerator done
//
// PRIORITY ENCODING (highest to lowest):
//   1. Fast interrupts: 31 → 16 (descending)
//   2. Reserved bits: 15 → 12
//   3. Machine External: 11 (MEI)
//   4. Machine Software: 3 (MSI)
//   5. Machine Timer: 7 (MTI)
//   6. Remaining reserved: 10, 2, 6, 9, 1, 5, 8, 0, 4
//
// INTERRUPT QUALIFICATION:
//   Three-level filtering before interrupt taken:
//     1. IRQ_MASK: Compile-time mask (removes unsupported interrupts)
//     2. MIE CSR: Software mask (per-bit interrupt enable)
//     3. Global enable: mstatus.MIE (M-mode) or mstatus.UIE (U-mode if PULP_SECURE)
//
// WAKE-UP FUNCTIONALITY:
//   irq_wu_ctrl_o based on UNREGISTERED irq_i
//   Allows wake from WFI even when clk_gated_o disabled
//   Critical for low-power operation
//
// SECURITY (PULP_SECURE=1):
//   Adds interrupt secure bit (irq_sec_i)
//   Modifies global enable logic for User/Machine mode distinction
//   Allows U-mode interrupts when u_ie_i set
//
// TIMING:
//   Interrupt latency = 1 cycle (registration) + controller FSM latency
//   Fast interrupts optimized for minimal cycles to handler entry
//
// INTERFACE WITH CONTROLLER:
//   irq_req_ctrl_o: Request to take interrupt
//   irq_id_ctrl_o: Which interrupt to take (encoded priority)
//   irq_sec_ctrl_o: Security level of interrupt
//   Controller decides when safe to take interrupt (no hazards)
//
///////////////////////////////////////////////////////////////////////////////

module cv32e40p_int_controller
  import cv32e40p_pkg::*;
#(
    // PULP_SECURE: Enable User/Machine mode security features
    // 0: Machine mode only, simpler interrupt enable logic
    // 1: U/M mode support, separate interrupt enable bits
    parameter PULP_SECURE = 0
) (
    // Clock and Reset
    input logic clk,      // Gated clock (from sleep unit)
    input logic rst_n,    // Active-low reset

    ///////////////////////////////////////////////////////////////////////////
    // External Interrupt Inputs
    ///////////////////////////////////////////////////////////////////////////
    
    // 32-bit interrupt vector
    // Level-triggered: Held high until serviced
    // Bit mapping:
    //   [31:16] - Fast custom interrupts (PULP extension)
    //   [15:12] - Reserved (masked by IRQ_MASK)
    //   [11]    - MEI (Machine External Interrupt)
    //   [10:8]  - Reserved
    //   [7]     - MTI (Machine Timer Interrupt)
    //   [6:4]   - Reserved
    //   [3]     - MSI (Machine Software Interrupt)
    //   [2:0]   - Reserved
    input logic [31:0] irq_i,
    
    // Interrupt security level (PULP_SECURE only)
    // From Event Unit in PULP cluster
    // Indicates if interrupt should be delivered to U-mode
    input logic        irq_sec_i,

    ///////////////////////////////////////////////////////////////////////////
    // Outputs to Controller FSM
    ///////////////////////////////////////////////////////////////////////////
    
    // Interrupt request - instructs controller to take interrupt
    // Asserted when: (qualified interrupt pending) AND (global enable)
    output logic       irq_req_ctrl_o,
    
    // Interrupt security level (registered)
    // Passed to controller for privilege level handling
    output logic       irq_sec_ctrl_o,
    
    // Interrupt ID - which interrupt to service (5-bit encoding)
    // Priority-encoded from irq_local_qual
    // Controller writes this to mcause CSR
    output logic [4:0] irq_id_ctrl_o,
    
    // Wake-up signal - unregistered interrupt indication
    // Used by sleep unit to wake from WFI
    // Based on raw irq_i (not registered) to minimize wake latency
    output logic       irq_wu_ctrl_o,

    ///////////////////////////////////////////////////////////////////////////
    // Interface with CSR Module
    ///////////////////////////////////////////////////////////////////////////
    
    // MIE (Machine Interrupt Enable) CSR - bypass path
    // Per-bit interrupt enables
    // Bypass to avoid CSR read latency in interrupt path
    input  logic     [31:0] mie_bypass_i,
    
    // MIP (Machine Interrupt Pending) CSR
    // Read-only view of registered interrupt inputs
    // Software reads this to determine pending interrupts
    output logic     [31:0] mip_o,
    
    // Global interrupt enable bits from mstatus CSR
    // m_ie_i: mstatus.MIE - Machine mode interrupt enable
    // u_ie_i: mstatus.UIE - User mode interrupt enable (PULP_SECURE only)
    input  logic            m_ie_i,
    input  logic            u_ie_i,
    
    // Current privilege level (PULP_SECURE only)
    // Determines which global enable bit applies
    input  PrivLvl_t        current_priv_lvl_i
);

  ///////////////////////////////////////////////////////////////////////////
  // INTERNAL SIGNALS
  ///////////////////////////////////////////////////////////////////////////
  
  // Global interrupt enable (combines privilege level and mstatus bits)
  logic        global_irq_enable;
  
  // Locally qualified interrupts (irq_q AND mie_bypass_i)
  // These are the interrupts actually eligible to be taken
  logic [31:0] irq_local_qual;
  
  // Registered interrupt inputs (on gated clock)
  // Used throughout module to avoid timing paths from irq_i
  logic [31:0] irq_q;
  
  // Registered security level
  logic        irq_sec_q;

  ///////////////////////////////////////////////////////////////////////////
  // INTERRUPT INPUT REGISTRATION
  ///////////////////////////////////////////////////////////////////////////
  // Register all interrupt inputs on gated clock
  //
  // WHY REGISTER:
  //   1. Timing: Breaks long paths from irq_i pins to instruction outputs
  //   2. Stability: Ensures interrupt state stable for priority encoding
  //   3. MIP CSR: Provides registered view for software reads
  //
  // WAKE-UP EXCEPTION:
  //   irq_wu_ctrl_o uses UNREGISTERED irq_i
  //   Allows wake-up even when clk is gated
  //   Sleep unit monitors irq_i directly for zero-latency wake
  //
  // IRQ_MASK:
  //   Compile-time mask from cv32e40p_pkg
  //   Removes unsupported interrupt bits (typically reserved bits)
  //   Example: IRQ_MASK = 32'hFFFF_0888 enables fast IRQs and standard M-mode IRQs
  //
  // Register all interrupt inputs (on gated clock). The wake-up logic will
  // observe irq_i as well, but in all other places irq_q will be used to 
  // avoid timing paths from irq_i to instr_*_o

  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      irq_q     <= '0;
      irq_sec_q <= 1'b0;
    end else begin
      // Apply IRQ_MASK to filter out unsupported interrupt bits
      irq_q     <= irq_i & IRQ_MASK;
      irq_sec_q <= irq_sec_i;
    end
  end

  ///////////////////////////////////////////////////////////////////////////
  // MIP CSR (MACHINE INTERRUPT PENDING)
  ///////////////////////////////////////////////////////////////////////////
  // Provides software read-only view of pending interrupts
  // Registered version ensures stable CSR reads
  // Software typically:
  //   1. Read MIP to see which interrupts pending
  //   2. Read MIE to see which are enabled
  //   3. Set/clear MIE bits to mask/unmask interrupts
  // MIP CSR
  assign mip_o = irq_q;

  ///////////////////////////////////////////////////////////////////////////
  // LOCAL INTERRUPT QUALIFICATION
  ///////////////////////////////////////////////////////////////////////////
  // Combine pending interrupts with software enables
  // Result: Interrupts that are both pending AND enabled
  //
  // TWO-LEVEL MASKING:
  //   1. IRQ_MASK: Hardware mask (compile-time, removes unsupported IRQs)
  //   2. MIE CSR: Software mask (run-time, per-bit enable)
  //
  // irq_local_qual used for:
  //   - Interrupt request generation (any bit set → request)
  //   - Priority encoding (which interrupt to take)
  //
  // Qualify registered IRQ with MIE CSR to compute locally enabled IRQs
  assign irq_local_qual = irq_q & mie_bypass_i;

  ///////////////////////////////////////////////////////////////////////////
  // WAKE-UP SIGNAL
  ///////////////////////////////////////////////////////////////////////////
  // Based on UNREGISTERED irq_i for minimum latency
  // Critical for wake-from-sleep:
  //   - WFI stops clock (clk_gated_o = 0)
  //   - irq_q can't update (no clock edges)
  //   - irq_wu_ctrl_o monitors irq_i directly
  //   - Sleep unit uses this to re-enable clock
  //
  // Wake condition: ANY enabled interrupt asserted
  // Even if global interrupts disabled, can wake from WFI
  //
  // Wake-up signal based on unregistered IRQ such that wake-up can be caused if no clock is present
  assign irq_wu_ctrl_o = |(irq_i & mie_bypass_i);

  ///////////////////////////////////////////////////////////////////////////
  // GLOBAL INTERRUPT ENABLE
  ///////////////////////////////////////////////////////////////////////////
  // Determines if interrupts can be taken based on:
  //   - Current privilege level
  //   - Interrupt enable bits in mstatus CSR
  //
  // PULP_SECURE=0 (Machine mode only):
  //   global_enable = mstatus.MIE
  //   Simple: Only M-mode, single enable bit
  //
  // PULP_SECURE=1 (User + Machine modes):
  //   In U-mode: global_enable = mstatus.UIE OR irq_sec_i
  //     - U-mode interrupts enabled by mstatus.UIE
  //     - Secure interrupts (irq_sec_i) can override
  //   In M-mode: global_enable = mstatus.MIE
  //     - M-mode interrupts enabled by mstatus.MIE
  //
  // RISC-V BEHAVIOR:
  //   Interrupts disabled when:
  //     - In trap handler (before mstatus.MIE restored)
  //     - Software explicitly clears mstatus.MIE
  //     - Debug mode active (handled in controller)
  //
  // Global interrupt enable
  generate
    if (PULP_SECURE) begin : gen_pulp_secure
      // U-mode: Enable if (UIE set) OR (interrupt is secure)
      // M-mode: Enable if MIE set
      assign global_irq_enable = ((u_ie_i || irq_sec_i) && current_priv_lvl_i == PRIV_LVL_U) || (m_ie_i && current_priv_lvl_i == PRIV_LVL_M);
    end else begin : gen_no_pulp_secure
      // Machine mode only: Simple MIE check
      assign global_irq_enable = m_ie_i;
    end
  endgenerate

  ///////////////////////////////////////////////////////////////////////////
  // INTERRUPT REQUEST GENERATION
  ///////////////////////////////////////////////////////////////////////////
  // Request interrupt when:
  //   1. At least one locally qualified interrupt pending, AND
  //   2. Global interrupts enabled
  //
  // Controller will:
  //   - Check for pipeline hazards
  //   - Decide when safe to take interrupt
  //   - Save PC to mepc
  //   - Jump to trap vector
  //   - Write mcause with irq_id_ctrl_o
  //
  // Request to take interrupt if there is a locally enabled interrupt while interrupts are also enabled globally
  assign irq_req_ctrl_o = (|irq_local_qual) && global_irq_enable;

  ///////////////////////////////////////////////////////////////////////////
  // INTERRUPT PRIORITY ENCODER
  ///////////////////////////////////////////////////////////////////////////
  // Encodes 32-bit interrupt vector to 5-bit interrupt ID
  // Priority: Highest bit number = Highest priority
  //
  // PRIORITY ORDER (highest to lowest):
  //   Tier 1: Fast Custom Interrupts [31:16]
  //     - Highest priority for low-latency response
  //     - Typical: DMA, accelerators, real-time events
  //     - Priority within tier: 31 > 30 > ... > 16
  //
  //   Tier 2: Reserved [15:12]
  //     - Future expansion, currently masked by IRQ_MASK
  //
  //   Tier 3: Standard Machine Interrupts
  //     [11] MEI - Machine External Interrupt
  //     [3]  MSI - Machine Software Interrupt
  //     [7]  MTI - Machine Timer Interrupt
  //     RISC-V standard: MEI > MSI > MTI
  //
  //   Tier 4: Reserved lower bits
  //     Various reserved interrupt sources
  //     Masked by default, available for custom extensions
  //
  // ENCODING METHOD:
  //   Combinational priority encoder (if-else chain)
  //   Check each bit from highest to lowest
  //   First asserted bit determines interrupt ID
  //
  // ALTERNATIVE IMPLEMENTATIONS:
  //   1. Find-first-one (FFO) tree: Faster, more area
  //   2. Configurable priority: More flexible, complex
  //   3. Round-robin: Fair but doesn't match RISC-V spec
  //
  // OUTPUT:
  //   irq_id_ctrl_o = 5-bit interrupt ID
  //   Controller writes this to mcause[4:0]
  //   Software reads mcause to determine interrupt source
  //
  // DEFAULT VALUE:
  //   If no interrupts (shouldn't happen when irq_req_ctrl_o=1):
  //     Return CSR_MTIX_BIT (7) as safe default
  //
  // Interrupt Encoder
  //
  // - sets correct id to request to ID
  // - encodes priority order

  always_comb begin
    // Tier 1: Fast custom interrupts [31:16] - Highest priority
    if (irq_local_qual[31]) irq_id_ctrl_o = 5'd31;  // Custom irq_i[31]
    else if (irq_local_qual[30]) irq_id_ctrl_o = 5'd30;  // Custom irq_i[30]
    else if (irq_local_qual[29]) irq_id_ctrl_o = 5'd29;  // Custom irq_i[29]
    else if (irq_local_qual[28]) irq_id_ctrl_o = 5'd28;  // Custom irq_i[28]
    else if (irq_local_qual[27]) irq_id_ctrl_o = 5'd27;  // Custom irq_i[27]
    else if (irq_local_qual[26]) irq_id_ctrl_o = 5'd26;  // Custom irq_i[26]
    else if (irq_local_qual[25]) irq_id_ctrl_o = 5'd25;  // Custom irq_i[25]
    else if (irq_local_qual[24]) irq_id_ctrl_o = 5'd24;  // Custom irq_i[24]
    else if (irq_local_qual[23]) irq_id_ctrl_o = 5'd23;  // Custom irq_i[23]
    else if (irq_local_qual[22]) irq_id_ctrl_o = 5'd22;  // Custom irq_i[22]
    else if (irq_local_qual[21]) irq_id_ctrl_o = 5'd21;  // Custom irq_i[21]
    else if (irq_local_qual[20]) irq_id_ctrl_o = 5'd20;  // Custom irq_i[20]
    else if (irq_local_qual[19]) irq_id_ctrl_o = 5'd19;  // Custom irq_i[19]
    else if (irq_local_qual[18]) irq_id_ctrl_o = 5'd18;  // Custom irq_i[18]
    else if (irq_local_qual[17]) irq_id_ctrl_o = 5'd17;  // Custom irq_i[17]
    else if (irq_local_qual[16]) irq_id_ctrl_o = 5'd16;  // Custom irq_i[16]

    // Tier 2: Reserved bits [15:12] - Future expansion
    else if (irq_local_qual[15])
      irq_id_ctrl_o = 5'd15;  // Reserved  (default masked out with IRQ_MASK)
    else if (irq_local_qual[14])
      irq_id_ctrl_o = 5'd14;  // Reserved  (default masked out with IRQ_MASK)
    else if (irq_local_qual[13])
      irq_id_ctrl_o = 5'd13;  // Reserved  (default masked out with IRQ_MASK)
    else if (irq_local_qual[12])
      irq_id_ctrl_o = 5'd12;  // Reserved  (default masked out with IRQ_MASK)

    // Tier 3: Standard RISC-V Machine interrupts
    // Priority: External > Software > Timer (RISC-V convention)
    else if (irq_local_qual[CSR_MEIX_BIT]) irq_id_ctrl_o = CSR_MEIX_BIT;  // MEI, irq_i[11]
    else if (irq_local_qual[CSR_MSIX_BIT]) irq_id_ctrl_o = CSR_MSIX_BIT;  // MSI, irq_i[3]
    else if (irq_local_qual[CSR_MTIX_BIT]) irq_id_ctrl_o = CSR_MTIX_BIT;  // MTI, irq_i[7]

    // Tier 4: Reserved bits related to standard interrupts
    // Assuming EI, SI, TI priority ordering for reserved bits
    else if (irq_local_qual[10])
      irq_id_ctrl_o = 5'd10;                         // Reserved (for now assuming EI, SI, TI priority) (default masked out with IRQ_MASK)
    else if (irq_local_qual[2])
      irq_id_ctrl_o = 5'd2;                          // Reserved (for now assuming EI, SI, TI priority) (default masked out with IRQ_MASK)
    else if (irq_local_qual[6])
      irq_id_ctrl_o = 5'd6;                          // Reserved (for now assuming EI, SI, TI priority) (default masked out with IRQ_MASK)

    // Tier 5: Supervisor-mode interrupts (if S-mode supported)
    // Currently reserved, masked by IRQ_MASK
    else if (irq_local_qual[9])
      irq_id_ctrl_o = 5'd9;  // Reserved: SEI (default masked out with IRQ_MASK)
    else if (irq_local_qual[1])
      irq_id_ctrl_o = 5'd1;  // Reserved: SSI (default masked out with IRQ_MASK)
    else if (irq_local_qual[5])
      irq_id_ctrl_o = 5'd5;  // Reserved: STI (default masked out with IRQ_MASK)

    // Tier 6: User-mode interrupts (if U-mode interrupts supported)
    // Currently reserved, masked by IRQ_MASK
    else if (irq_local_qual[8])
      irq_id_ctrl_o = 5'd8;  // Reserved: UEI (default masked out with IRQ_MASK)
    else if (irq_local_qual[0])
      irq_id_ctrl_o = 5'd0;  // Reserved: USI (default masked out with IRQ_MASK)
    else if (irq_local_qual[4])
      irq_id_ctrl_o = 5'd4;  // Reserved: UTI (default masked out with IRQ_MASK)

    // Default: Should never reach here if irq_req_ctrl_o asserted correctly
    // Return safe value (MTI bit) if no interrupt found
    else irq_id_ctrl_o = CSR_MTIX_BIT;  // Value not relevant
  end

  ///////////////////////////////////////////////////////////////////////////
  // INTERRUPT SECURITY OUTPUT
  ///////////////////////////////////////////////////////////////////////////
  // Pass registered security bit to controller
  // Controller uses this for privilege level decisions
  assign irq_sec_ctrl_o = irq_sec_q;

  ///////////////////////////////////////////////////////////////////////////
  // END OF MODULE
  ///////////////////////////////////////////////////////////////////////////
  //
  // INTERRUPT CONTROLLER SUMMARY:
  //
  // KEY FEATURES:
  //   - 32 interrupt sources (16 standard + 16 fast custom)
  //   - Priority-based encoding (highest bit = highest priority)
  //   - Three-level qualification: IRQ_MASK, MIE CSR, global enable
  //   - Fast wake-up from sleep (unregistered irq_i monitoring)
  //   - Security support (PULP_SECURE mode)
  //
  // INTERRUPT LATENCY:
  //   Minimum cycles from assertion to handler entry:
  //     1 cycle:  Interrupt registration (irq_q)
  //     1 cycle:  Controller recognizes request
  //     2-3 cycles: Pipeline flush and PC save
  //     1 cycle:  Jump to trap vector
  //     Total: ~5-6 cycles for fast interrupts
  //
  // FAST INTERRUPTS:
  //   Bits [31:16] optimized for low latency:
  //     - Highest priority in encoder
  //     - Vectored directly (no decoding delay)
  //     - Typical use: Real-time control, DMA events
  //
  // SOFTWARE INTERFACE:
  //   Trap handler reads mcause CSR to get irq_id_ctrl_o
  //   Decodes interrupt ID to determine source
  //   Services interrupt (may clear external source)
  //   Returns via MRET instruction
  //
  // ALTERNATIVE IMPLEMENTATIONS:
  //   1. Configurable priority: Allow software to set priorities
  //   2. Nested interrupts: Take higher priority IRQ while in handler
  //   3. Vectored interrupts: Direct jump to per-interrupt handler
  //   4. Threshold-based: Only take interrupts above threshold level
  //

endmodule  // cv32e40p_int_controller
