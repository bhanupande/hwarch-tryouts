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
//                 Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                 Andrea Bettati - andrea.bettati@studenti.unipr.it          //
//                                                                            //
// Design Name:    Control and Status Registers                               //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Control and Status Registers (CSRs) loosely following the  //
//                 RiscV draft priviledged instruction set spec (v1.9)        //
//                 Added Floating point support                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// CV32E40P CONTROL AND STATUS REGISTERS (CSRs)
///////////////////////////////////////////////////////////////////////////////
//
// This module implements the RISC-V Control and Status Registers (CSRs) for
// the CV32E40P core. It manages all architectural state beyond the general-
// purpose register file, including:
//
// MACHINE MODE CSRs:
// - mstatus, misa, mie, mtvec, mepc, mcause, mip: Standard M-mode CSRs
// - mvendorid, marchid, mimpid, mhartid: Machine information registers
// - mscratch: Scratch register for M-mode trap handlers
//
// USER MODE CSRs (when PULP_SECURE=1):
// - ustatus, uie, utvec, uepc, ucause: Standard U-mode CSRs
// - uscratch: Scratch register for U-mode trap handlers
//
// FLOATING-POINT CSRs (when FPU=1):
// - fflags, frm, fcsr: IEEE 754 rounding mode and exception flags
// - fs field in mstatus: Floating-point unit state
//
// HARDWARE LOOP CSRs (when COREV_PULP=1):
// - lpstart[0:1], lpend[0:1], lpcount[0:1]: Two hardware loop registers
//
// PHYSICAL MEMORY PROTECTION (when USE_PMP=1):
// - pmpcfg[0:3], pmpaddr[0:15]: Up to 16 PMP entries for memory protection
//
// PERFORMANCE MONITORING (when NUM_MHPMCOUNTERS>0):
// - mcycle, minstret: Base counters (when PULP_PERF_COUNTERS=0)
// - mhpmcounter[3:31], mhpmevent[3:31]: Hardware performance counters
// - mcounteren: Counter enable register (when PULP_SECURE=1)
//
// DEBUG CSRs (Debug Spec 0.13.2):
// - dcsr: Debug control and status
// - dpc: Debug program counter
// - dscratch[0:1]: Debug scratch registers
//
// TRIGGER CSRs (when DEBUG_TRIGGER_EN=1):
// - tselect, tdata[1:3], tinfo: Trigger module interface
//
// KEY FEATURES:
// - SRAM-like CSR access interface with address, write data, operation
// - Atomic CSR operations: CSRRW, CSRRS, CSRRC
// - Exception and interrupt handling with privilege level management
// - Performance counter infrastructure with 16 event types
// - Debug mode support with single-step capability
// - Hardware loop support for PULP ISA extensions
// - PMP enforcement for secure configurations
//
// CSR NUMBERING:
// Follows RISC-V privileged spec v1.11 with custom extensions for PULP
// 
///////////////////////////////////////////////////////////////////////////////

module cv32e40p_cs_registers
  import cv32e40p_pkg::*;
#(
    parameter N_HWLP           = 2,   // Number of hardware loops (0-2)
    parameter APU              = 0,   // Enable APU (not used in CSRs)
    parameter A_EXTENSION      = 0,   // Atomic extension support
    parameter FPU              = 0,   // Enable FPU CSRs (fflags, frm, fcsr)
    parameter ZFINX            = 0,   // FPU uses integer registers (affects misa)
    parameter PULP_SECURE      = 0,   // Enable U-mode and security features
    parameter USE_PMP          = 0,   // Enable Physical Memory Protection
    parameter N_PMP_ENTRIES    = 16,  // Number of PMP entries (max 16)
    parameter NUM_MHPMCOUNTERS = 1,   // Number of performance counters (0-29)
    parameter COREV_PULP       = 0,   // Enable PULP ISA extensions
    parameter COREV_CLUSTER    = 0,   // Enable cluster support (affects misa)
    parameter DEBUG_TRIGGER_EN = 1    // Enable debug trigger module
) (
    ///////////////////////////////////////////////////////////////////////////
    // CLOCK AND RESET
    ///////////////////////////////////////////////////////////////////////////
    input logic clk,                               // System clock
    input logic rst_n,                             // Active-low asynchronous reset

    ///////////////////////////////////////////////////////////////////////////
    // CONFIGURATION
    ///////////////////////////////////////////////////////////////////////////
    input  logic [31:0] hart_id_i,                 // Hardware thread ID (mhartid CSR)
    
    // Trap vector base addresses (upper 24 bits)
    output logic [23:0] mtvec_o,                   // M-mode trap vector base
    output logic [23:0] utvec_o,                   // U-mode trap vector base
    output logic [ 1:0] mtvec_mode_o,              // M-mode vector mode (0=direct, 1=vectored)
    output logic [ 1:0] utvec_mode_o,              // U-mode vector mode

    // MTVEC initialization (from boot address)
    input logic [31:0] mtvec_addr_i,               // Initial mtvec value
    input logic        csr_mtvec_init_i,           // Initialize mtvec from boot address

    ///////////////////////////////////////////////////////////////////////////
    // CSR ACCESS INTERFACE (SRAM-like)
    ///////////////////////////////////////////////////////////////////////////
    input  csr_num_e           csr_addr_i,         // CSR address (12-bit encoded as enum)
    input  logic        [31:0] csr_wdata_i,        // CSR write data
    input  csr_opcode_e        csr_op_i,           // CSR operation (RW, RS, RC, none)
    output logic        [31:0] csr_rdata_o,        // CSR read data

    ///////////////////////////////////////////////////////////////////////////
    // FLOATING-POINT CSRs (FPU=1)
    ///////////////////////////////////////////////////////////////////////////
    output logic               fs_off_o,           // FPU disabled (mstatus.FS == 0)
    output logic [        2:0] frm_o,              // Rounding mode from fcsr
    input  logic [C_FFLAG-1:0] fflags_i,           // Exception flags from FPU
    input  logic               fflags_we_i,        // Write enable for fflags
    input  logic               fregs_we_i,         // FP register write (sets FS=dirty)

    ///////////////////////////////////////////////////////////////////////////
    // INTERRUPT CONTROL
    ///////////////////////////////////////////////////////////////////////////
    output logic [31:0] mie_bypass_o,              // MIE CSR value (for immediate use)
    input  logic [31:0] mip_i,                     // Pending interrupts from core
    output logic        m_irq_enable_o,            // M-mode interrupts enabled (MIE bit)
    output logic        u_irq_enable_o,            // U-mode interrupts enabled (UIE bit)

    // Secure interrupts (PULP_SECURE=1)
    input  logic        csr_irq_sec_i,             // Secure interrupt flag
    output logic        sec_lvl_o,                 // Current security level
    
    // Exception PC registers
    output logic [31:0] mepc_o,                    // M-mode exception PC
    output logic [31:0] uepc_o,                    // U-mode exception PC
    
    // Counter enable (PULP_SECURE=1)
    output logic [31:0] mcounteren_o,              // Counter enable for U-mode

    ///////////////////////////////////////////////////////////////////////////
    // DEBUG MODE
    ///////////////////////////////////////////////////////////////////////////
    input  logic        debug_mode_i,              // Currently in debug mode
    input  logic [ 2:0] debug_cause_i,             // Debug entry cause
    input  logic        debug_csr_save_i,          // Save PC to dpc
    output logic [31:0] depc_o,                    // Debug exception PC (dpc CSR)
    output logic        debug_single_step_o,       // Single-step enable (dcsr.step)
    output logic        debug_ebreakm_o,           // EBREAK enters debug in M-mode
    output logic        debug_ebreaku_o,           // EBREAK enters debug in U-mode
    output logic        trigger_match_o,           // Trigger fired

    ///////////////////////////////////////////////////////////////////////////
    // PHYSICAL MEMORY PROTECTION (USE_PMP=1)
    ///////////////////////////////////////////////////////////////////////////
    output logic [N_PMP_ENTRIES-1:0][31:0] pmp_addr_o,  // PMP address registers
    output logic [N_PMP_ENTRIES-1:0][ 7:0] pmp_cfg_o,   // PMP configuration registers

    ///////////////////////////////////////////////////////////////////////////
    // PRIVILEGE LEVEL
    ///////////////////////////////////////////////////////////////////////////
    output PrivLvl_t priv_lvl_o,                   // Current privilege level (M/U)

    ///////////////////////////////////////////////////////////////////////////
    // EXCEPTION/INTERRUPT HANDLING
    ///////////////////////////////////////////////////////////////////////////
    // PC values from pipeline stages (for saving to [m/u]epc on exception)
    input logic [31:0] pc_if_i,                    // PC in IF stage
    input logic [31:0] pc_id_i,                    // PC in ID stage
    input logic [31:0] pc_ex_i,                    // PC in EX stage

    // Exception save signals (save PC to [m/u]epc)
    input logic csr_save_if_i,                     // Save PC from IF stage
    input logic csr_save_id_i,                     // Save PC from ID stage
    input logic csr_save_ex_i,                     // Save PC from EX stage

    // Exception return signals
    input logic csr_restore_mret_i,                // MRET instruction (return from M-mode)
    input logic csr_restore_uret_i,                // URET instruction (return from U-mode)
    input logic csr_restore_dret_i,                // DRET instruction (return from debug)

    // Exception cause
    input logic [       5:0]       csr_cause_i,    // Exception/interrupt cause code
    input logic                    csr_save_cause_i,  // Save cause to [m/u]cause

    ///////////////////////////////////////////////////////////////////////////
    // HARDWARE LOOPS (COREV_PULP=1)
    ///////////////////////////////////////////////////////////////////////////
    input logic [N_HWLP-1:0][31:0] hwlp_start_i,   // Hardware loop start addresses
    input logic [N_HWLP-1:0][31:0] hwlp_end_i,     // Hardware loop end addresses
    input logic [N_HWLP-1:0][31:0] hwlp_cnt_i,     // Hardware loop counters

    ///////////////////////////////////////////////////////////////////////////
    // PERFORMANCE COUNTER EVENTS
    ///////////////////////////////////////////////////////////////////////////
    input logic mhpmevent_minstret_i,              // Instruction retired
    input logic mhpmevent_load_i,                  // Load instruction
    input logic mhpmevent_store_i,                 // Store instruction
    input logic mhpmevent_jump_i,                  // Jump instruction retired (j, jr, jal, jalr)
    input logic mhpmevent_branch_i,                // Branch instruction retired (beq, bne, etc.)
    input logic mhpmevent_branch_taken_i,          // Branch instruction taken
    input logic mhpmevent_compressed_i,            // Compressed instruction
    input logic mhpmevent_jr_stall_i,              // Jump register stall
    input logic mhpmevent_imiss_i,                 // Instruction cache miss
    input logic mhpmevent_ld_stall_i,              // Load use hazard stall
    input logic mhpmevent_pipe_stall_i,            // Pipeline stall
    input logic apu_typeconflict_i,                // APU type conflict
    input logic apu_contention_i,                  // APU contention
    input logic apu_dep_i,                         // APU dependency stall
    input logic apu_wb_i                           // APU writeback
);

  ///////////////////////////////////////////////////////////////////////////
  // LOCAL PARAMETERS
  ///////////////////////////////////////////////////////////////////////////
  
  // Performance counter configuration
  localparam NUM_HPM_EVENTS = 16;                  // Number of different performance events

  // Trap vector mode (vectored interrupts)
  localparam MTVEC_MODE = 2'b01;                   // Mode 1 = vectored

  // PMP configuration limits
  localparam MAX_N_PMP_ENTRIES = 16;               // Maximum PMP entries (RISC-V spec)
  localparam MAX_N_PMP_CFG = 4;                    // Maximum PMP config registers (4 bytes each)
  localparam N_PMP_CFG = N_PMP_ENTRIES % 4 == 0 ? N_PMP_ENTRIES / 4 : N_PMP_ENTRIES / 4 + 1;

  // MSTATUS register bit positions
  localparam MSTATUS_UIE_BIT = 0;                  // U-mode interrupt enable
  localparam MSTATUS_SIE_BIT = 1;                  // S-mode interrupt enable
  localparam MSTATUS_MIE_BIT = 3;                  // M-mode interrupt enable
  localparam MSTATUS_UPIE_BIT = 4;                 // U-mode previous interrupt enable
  localparam MSTATUS_SPIE_BIT = 5;                 // S-mode previous interrupt enable
  localparam MSTATUS_MPIE_BIT = 7;                 // M-mode previous interrupt enable
  localparam MSTATUS_SPP_BIT = 8;                  // S-mode previous privilege
  localparam MSTATUS_MPP_BIT_LOW = 11;             // M-mode previous privilege (low bit)
  localparam MSTATUS_MPP_BIT_HIGH = 12;            // M-mode previous privilege (high bit)
  localparam MSTATUS_FS_BIT_LOW = 13;              // FPU status (low bit)
  localparam MSTATUS_FS_BIT_HIGH = 14;             // FPU status (high bit)
  localparam MSTATUS_MPRV_BIT = 17;                // Modify privilege (load/store use MPP)
  localparam MSTATUS_SD_BIT = 31;                  // State dirty (FS=dirty)

  // MISA register value (read-only, identifies ISA extensions)
  localparam logic [1:0] MXL = 2'd1;               // M-XLEN: RV32 = 1
  localparam logic [31:0] MISA_VALUE = 
    (32'(A_EXTENSION) << 0)                        // A - Atomic Instructions extension
    | (1 << 2)                                     // C - Compressed extension
    | (0 << 3)                                     // D - Double precision floating-point
    | (0 << 4)                                     // E - RV32E base ISA
    | (32'(FPU == 1 && ZFINX == 0) << 5)          // F - Single precision floating-point
    | (1 << 8)                                     // I - RV32I base ISA
    | (1 << 12)                                    // M - Integer Multiply/Divide extension
    | (0 << 13)                                    // N - User level interrupts
    | (0 << 18)                                    // S - Supervisor mode
    | (32'(PULP_SECURE) << 20)                    // U - User mode implemented
    | (32'(COREV_PULP || COREV_CLUSTER) << 23)    // X - Non-standard extensions present
    | (32'(MXL) << 30);                           // M-XLEN field

  // Performance counter mode: 
  // When set to 1, makes counters non-compliant (no mcycle/minstret, only HPMCOUNTERs)
  localparam PULP_PERF_COUNTERS = 0;

  ///////////////////////////////////////////////////////////////////////////
  // TYPE DEFINITIONS
  ///////////////////////////////////////////////////////////////////////////
  
  // PMP register structure
  typedef struct packed {
    logic [MAX_N_PMP_ENTRIES-1:0][31:0] pmpaddr;       // PMP address registers
    logic [MAX_N_PMP_CFG-1:0][31:0] pmpcfg_packed;     // PMP config packed (4 per register)
    logic [MAX_N_PMP_ENTRIES-1:0][7:0] pmpcfg;         // PMP config unpacked
  } Pmp_t;

  ///////////////////////////////////////////////////////////////////////////
  // INTERNAL SIGNAL DECLARATIONS
  ///////////////////////////////////////////////////////////////////////////
  
  // CSR access control signals
  logic [31:0] csr_wdata_int;                      // CSR write data (after operation decode)
  logic [31:0] csr_rdata_int;                      // CSR read data (multiplexed)
  logic        csr_we_int;                         // CSR write enable (internal)

  // Floating-Point CSRs (FPU=1)
  logic [C_RM-1:0] frm_q, frm_n;                   // Rounding mode register
  logic [C_FFLAG-1:0] fflags_q, fflags_n;          // Exception flags register
  logic fcsr_update;                               // FCSR update flag

  // Exception PC registers
  logic [31:0] mepc_q, mepc_n;                     // M-mode exception PC
  logic [31:0] uepc_q, uepc_n;                     // U-mode exception PC
  
  // Trigger module (DEBUG_TRIGGER_EN=1)
  logic [31:0] tmatch_control_rdata;               // Trigger match control read data
  logic [31:0] tmatch_value_rdata;                 // Trigger match value read data
  logic [15:0] tinfo_types;                        // Trigger info types
  
  // Debug CSRs
  Dcsr_t dcsr_q, dcsr_n;                           // Debug control and status
  logic [31:0] depc_q, depc_n;                     // Debug exception PC
  logic [31:0] dscratch0_q, dscratch0_n;           // Debug scratch 0
  logic [31:0] dscratch1_q, dscratch1_n;           // Debug scratch 1
  logic [31:0] mscratch_q, mscratch_n;             // M-mode scratch

  // Exception handling
  logic [31:0] exception_pc;                       // PC to save on exception
  Status_t mstatus_q, mstatus_n;                   // M-mode status register
  logic mstatus_we_int;                            // MSTATUS write enable
  FS_t mstatus_fs_q, mstatus_fs_n;                 // FPU status field
  logic [5:0] mcause_q, mcause_n;                  // M-mode exception cause
  logic [5:0] ucause_q, ucause_n;                  // U-mode exception cause
  logic [23:0] mtvec_n, mtvec_q;                   // M-mode trap vector base
  logic [23:0] utvec_n, utvec_q;                   // U-mode trap vector base
  logic [1:0] mtvec_mode_n, mtvec_mode_q;          // M-mode vector mode
  logic [1:0] utvec_mode_n, utvec_mode_q;          // U-mode vector mode

  // Interrupt control
  logic [31:0] mip;                                // Machine interrupt pending (masked)
  logic [31:0] mie_q, mie_n;                       // Machine interrupt enable (masked)

  logic [31:0] csr_mie_wdata;                      // MIE write data
  logic        csr_mie_we;                         // MIE write enable

  logic        is_irq;                             // Current exception is an interrupt
  
  // Privilege level
  PrivLvl_t priv_lvl_n, priv_lvl_q;                // Current/next privilege level

  // Physical Memory Protection
  Pmp_t pmp_reg_q, pmp_reg_n;                      // PMP register state
  logic [MAX_N_PMP_ENTRIES-1:0] pmpaddr_we;        // PMP address write enables (clock gating)
  logic [MAX_N_PMP_ENTRIES-1:0] pmpcfg_we;         // PMP config write enables (clock gating)

  // Performance Counters
  logic [31:0][MHPMCOUNTER_WIDTH-1:0] mhpmcounter_q;              // Performance counter values
  logic [31:0][31:0] mhpmevent_q, mhpmevent_n;                    // Performance event selectors
  logic [31:0] mcounteren_q, mcounteren_n;                        // Counter enable for U-mode
  logic [31:0] mcountinhibit_q, mcountinhibit_n;                  // Counter inhibit (disable counting)
  logic [NUM_HPM_EVENTS-1:0] hpm_events;                          // Performance event signals
  logic [31:0][MHPMCOUNTER_WIDTH-1:0] mhpmcounter_increment;      // Counter increment values
  logic [31:0] mhpmcounter_write_lower;                           // Write lower 32 bits of counter
  logic [31:0] mhpmcounter_write_upper;                           // Write upper 32 bits of counter
  logic [31:0] mhpmcounter_write_increment;                       // Write counter increment enable

  ///////////////////////////////////////////////////////////////////////////
  // INTERRUPT DETECTION
  ///////////////////////////////////////////////////////////////////////////
  
  // Decode interrupt vs exception from cause MSB
  assign is_irq = csr_cause_i[5];

  // Connect machine interrupt pending register
  assign mip = mip_i;

  ///////////////////////////////////////////////////////////////////////////
  // MIE CSR BYPASS LOGIC
  ///////////////////////////////////////////////////////////////////////////
  // The mie_n value is used instead of mie_q to allow a CSR write to MIE
  // to take effect immediately on the following instruction
  
  // MIE CSR operation decode
  always_comb begin
    csr_mie_wdata = csr_wdata_i;
    csr_mie_we    = 1'b1;

    case (csr_op_i)
      CSR_OP_WRITE: csr_mie_wdata = csr_wdata_i;           // CSRRW: write
      CSR_OP_SET:   csr_mie_wdata = csr_wdata_i | mie_q;   // CSRRS: set bits
      CSR_OP_CLEAR: csr_mie_wdata = (~csr_wdata_i) & mie_q; // CSRRC: clear bits
      CSR_OP_READ: begin
        csr_mie_wdata = csr_wdata_i;
        csr_mie_we    = 1'b0;                              // Read-only, no write
      end
    endcase
  end

  // Bypass MIE value when currently being written
  assign mie_bypass_o = ((csr_addr_i == CSR_MIE) && csr_mie_we) ? csr_mie_wdata & IRQ_MASK : mie_q;


  ///////////////////////////////////////////////////////////////////////////
  // CSR READ/WRITE LOGIC
  ///////////////////////////////////////////////////////////////////////////
  // NOTE: Any new CSR register added must also be added to the valid CSR
  //       register list in cv32e40p_decoder.sv

  genvar j;


  ///////////////////////////////////////////////////////////////////////////
  // CSR READ LOGIC
  ///////////////////////////////////////////////////////////////////////////
  // Multiplexes CSR read data based on address
  // Two versions: PULP_SECURE=1 (with U-mode CSRs) and PULP_SECURE=0 (M-mode only)
  
  if (PULP_SECURE == 1) begin : gen_pulp_secure_read_logic
    // Read logic with U-mode CSR support
    always_comb begin
      case (csr_addr_i)
        ///////////////////////////////////////////////////////////////////
        // FLOATING-POINT CSRs (FPU=1)
        ///////////////////////////////////////////////////////////////////
        CSR_FFLAGS: csr_rdata_int = (FPU == 1) ? {27'b0, fflags_q} : '0;  // FP exception flags
        CSR_FRM:    csr_rdata_int = (FPU == 1) ? {29'b0, frm_q} : '0;     // FP rounding mode
        CSR_FCSR:   csr_rdata_int = (FPU == 1) ? {24'b0, frm_q, fflags_q} : '0;  // FP control/status

        ///////////////////////////////////////////////////////////////////
        // MACHINE MODE CSRs
        ///////////////////////////////////////////////////////////////////
        // mstatus: Machine status register
        CSR_MSTATUS:
        csr_rdata_int = {
          14'b0,
          mstatus_q.mprv,           // [17] Modify privilege (loads/stores use MPP)
          4'b0,
          mstatus_q.mpp,            // [12:11] Previous privilege mode
          3'b0,
          mstatus_q.mpie,           // [7] Previous M-mode interrupt enable
          2'h0,
          mstatus_q.upie,           // [4] Previous U-mode interrupt enable
          mstatus_q.mie,            // [3] M-mode interrupt enable
          2'h0,
          mstatus_q.uie             // [0] U-mode interrupt enable
        };

        // misa: Machine ISA register (read-only, identifies supported extensions)
        CSR_MISA: csr_rdata_int = MISA_VALUE;

        // mie: Machine interrupt enable register
        CSR_MIE: begin
          csr_rdata_int = mie_q;
        end

        // mtvec: Machine trap-handler base address
        CSR_MTVEC: csr_rdata_int = {mtvec_q, 6'h0, mtvec_mode_q};
        
        // mscratch: Machine scratch register for trap handlers
        CSR_MSCRATCH: csr_rdata_int = mscratch_q;
        
        // mepc: Machine exception program counter
        CSR_MEPC: csr_rdata_int = mepc_q;
        
        // mcause: Machine exception cause
        CSR_MCAUSE: csr_rdata_int = {mcause_q[5], 26'b0, mcause_q[4:0]};
        
        // mip: Machine interrupt pending register
        CSR_MIP: begin
          csr_rdata_int = mip;
        end

        ///////////////////////////////////////////////////////////////////
        // MACHINE INFORMATION CSRs (read-only)
        ///////////////////////////////////////////////////////////////////
        CSR_MHARTID: csr_rdata_int = hart_id_i;  // Hardware thread ID
        CSR_MVENDORID: csr_rdata_int = {MVENDORID_BANK, MVENDORID_OFFSET};  // Vendor ID
        CSR_MARCHID: csr_rdata_int = MARCHID;    // Architecture ID
        
        // Unimplemented CSRs (read as 0)
        CSR_MIMPID, CSR_MTVAL: csr_rdata_int = 'b0;

        ///////////////////////////////////////////////////////////////////
        // COUNTER ENABLE CSR (PULP_SECURE=1)
        ///////////////////////////////////////////////////////////////////
        CSR_MCOUNTEREN: csr_rdata_int = mcounteren_q;  // Counter enable for U-mode

        ///////////////////////////////////////////////////////////////////
        // DEBUG/TRIGGER CSRs
        ///////////////////////////////////////////////////////////////////
        CSR_TSELECT, CSR_TDATA3, CSR_MCONTEXT, CSR_SCONTEXT: csr_rdata_int = 'b0;  // Not implemented
        CSR_TDATA1: csr_rdata_int = tmatch_control_rdata;  // Trigger match control
        CSR_TDATA2: csr_rdata_int = tmatch_value_rdata;    // Trigger match value
        CSR_TINFO: csr_rdata_int = tinfo_types;            // Trigger info

        // Debug CSRs (Debug Spec 0.13.2)
        CSR_DCSR: csr_rdata_int = dcsr_q;              // Debug control and status
        CSR_DPC: csr_rdata_int = depc_q;               // Debug PC
        CSR_DSCRATCH0: csr_rdata_int = dscratch0_q;    // Debug scratch 0
        CSR_DSCRATCH1: csr_rdata_int = dscratch1_q;    // Debug scratch 1

        ///////////////////////////////////////////////////////////////////
        // PERFORMANCE COUNTERS (lower 32 bits)
        // Includes mcycle, minstret, and mhpmcounter[3:31]
        // Also accessible from U-mode as cycle, instret, hpmcounter[3:31]
        ///////////////////////////////////////////////////////////////////
        CSR_MCYCLE,
      CSR_MINSTRET,
      CSR_MHPMCOUNTER3,
      CSR_MHPMCOUNTER4,  CSR_MHPMCOUNTER5,  CSR_MHPMCOUNTER6,  CSR_MHPMCOUNTER7,
      CSR_MHPMCOUNTER8,  CSR_MHPMCOUNTER9,  CSR_MHPMCOUNTER10, CSR_MHPMCOUNTER11,
      CSR_MHPMCOUNTER12, CSR_MHPMCOUNTER13, CSR_MHPMCOUNTER14, CSR_MHPMCOUNTER15,
      CSR_MHPMCOUNTER16, CSR_MHPMCOUNTER17, CSR_MHPMCOUNTER18, CSR_MHPMCOUNTER19,
      CSR_MHPMCOUNTER20, CSR_MHPMCOUNTER21, CSR_MHPMCOUNTER22, CSR_MHPMCOUNTER23,
      CSR_MHPMCOUNTER24, CSR_MHPMCOUNTER25, CSR_MHPMCOUNTER26, CSR_MHPMCOUNTER27,
      CSR_MHPMCOUNTER28, CSR_MHPMCOUNTER29, CSR_MHPMCOUNTER30, CSR_MHPMCOUNTER31,
      CSR_CYCLE,
      CSR_INSTRET,
      CSR_HPMCOUNTER3,
      CSR_HPMCOUNTER4,  CSR_HPMCOUNTER5,  CSR_HPMCOUNTER6,  CSR_HPMCOUNTER7,
      CSR_HPMCOUNTER8,  CSR_HPMCOUNTER9,  CSR_HPMCOUNTER10, CSR_HPMCOUNTER11,
      CSR_HPMCOUNTER12, CSR_HPMCOUNTER13, CSR_HPMCOUNTER14, CSR_HPMCOUNTER15,
      CSR_HPMCOUNTER16, CSR_HPMCOUNTER17, CSR_HPMCOUNTER18, CSR_HPMCOUNTER19,
      CSR_HPMCOUNTER20, CSR_HPMCOUNTER21, CSR_HPMCOUNTER22, CSR_HPMCOUNTER23,
      CSR_HPMCOUNTER24, CSR_HPMCOUNTER25, CSR_HPMCOUNTER26, CSR_HPMCOUNTER27,
      CSR_HPMCOUNTER28, CSR_HPMCOUNTER29, CSR_HPMCOUNTER30, CSR_HPMCOUNTER31:
        csr_rdata_int = mhpmcounter_q[csr_addr_i[4:0]][31:0];  // Lower 32 bits

        ///////////////////////////////////////////////////////////////////
        // PERFORMANCE COUNTERS (upper 32 bits)
        // High-word registers for 64-bit counter access in RV32
        ///////////////////////////////////////////////////////////////////
        ///////////////////////////////////////////////////////////////////
        // PERFORMANCE COUNTERS (upper 32 bits)
        // High-word registers for 64-bit counter access in RV32
        ///////////////////////////////////////////////////////////////////
        CSR_MCYCLEH,
      CSR_MINSTRETH,
      CSR_MHPMCOUNTER3H,
      CSR_MHPMCOUNTER4H,  CSR_MHPMCOUNTER5H,  CSR_MHPMCOUNTER6H,  CSR_MHPMCOUNTER7H,
      CSR_MHPMCOUNTER8H,  CSR_MHPMCOUNTER9H,  CSR_MHPMCOUNTER10H, CSR_MHPMCOUNTER11H,
      CSR_MHPMCOUNTER12H, CSR_MHPMCOUNTER13H, CSR_MHPMCOUNTER14H, CSR_MHPMCOUNTER15H,
      CSR_MHPMCOUNTER16H, CSR_MHPMCOUNTER17H, CSR_MHPMCOUNTER18H, CSR_MHPMCOUNTER19H,
      CSR_MHPMCOUNTER20H, CSR_MHPMCOUNTER21H, CSR_MHPMCOUNTER22H, CSR_MHPMCOUNTER23H,
      CSR_MHPMCOUNTER24H, CSR_MHPMCOUNTER25H, CSR_MHPMCOUNTER26H, CSR_MHPMCOUNTER27H,
      CSR_MHPMCOUNTER28H, CSR_MHPMCOUNTER29H, CSR_MHPMCOUNTER30H, CSR_MHPMCOUNTER31H,
      CSR_CYCLEH,
      CSR_INSTRETH,
      CSR_HPMCOUNTER3H,
      CSR_HPMCOUNTER4H,  CSR_HPMCOUNTER5H,  CSR_HPMCOUNTER6H,  CSR_HPMCOUNTER7H,
      CSR_HPMCOUNTER8H,  CSR_HPMCOUNTER9H,  CSR_HPMCOUNTER10H, CSR_HPMCOUNTER11H,
      CSR_HPMCOUNTER12H, CSR_HPMCOUNTER13H, CSR_HPMCOUNTER14H, CSR_HPMCOUNTER15H,
      CSR_HPMCOUNTER16H, CSR_HPMCOUNTER17H, CSR_HPMCOUNTER18H, CSR_HPMCOUNTER19H,
      CSR_HPMCOUNTER20H, CSR_HPMCOUNTER21H, CSR_HPMCOUNTER22H, CSR_HPMCOUNTER23H,
      CSR_HPMCOUNTER24H, CSR_HPMCOUNTER25H, CSR_HPMCOUNTER26H, CSR_HPMCOUNTER27H,
      CSR_HPMCOUNTER28H, CSR_HPMCOUNTER29H, CSR_HPMCOUNTER30H, CSR_HPMCOUNTER31H:
        csr_rdata_int = mhpmcounter_q[csr_addr_i[4:0]][63:32];  // Upper 32 bits

        ///////////////////////////////////////////////////////////////////
        // PERFORMANCE COUNTER CONTROL CSRs
        ///////////////////////////////////////////////////////////////////
        CSR_MCOUNTINHIBIT: csr_rdata_int = mcountinhibit_q;  // Counter inhibit (disable)

        // Performance event selectors: which events increment each counter
        CSR_MHPMEVENT3,
      CSR_MHPMEVENT4,  CSR_MHPMEVENT5,  CSR_MHPMEVENT6,  CSR_MHPMEVENT7,
      CSR_MHPMEVENT8,  CSR_MHPMEVENT9,  CSR_MHPMEVENT10, CSR_MHPMEVENT11,
      CSR_MHPMEVENT12, CSR_MHPMEVENT13, CSR_MHPMEVENT14, CSR_MHPMEVENT15,
      CSR_MHPMEVENT16, CSR_MHPMEVENT17, CSR_MHPMEVENT18, CSR_MHPMEVENT19,
      CSR_MHPMEVENT20, CSR_MHPMEVENT21, CSR_MHPMEVENT22, CSR_MHPMEVENT23,
      CSR_MHPMEVENT24, CSR_MHPMEVENT25, CSR_MHPMEVENT26, CSR_MHPMEVENT27,
      CSR_MHPMEVENT28, CSR_MHPMEVENT29, CSR_MHPMEVENT30, CSR_MHPMEVENT31:
        csr_rdata_int = mhpmevent_q[csr_addr_i[4:0]];

        ///////////////////////////////////////////////////////////////////
        // HARDWARE LOOP CSRs (COREV_PULP=1, non-standard)
        ///////////////////////////////////////////////////////////////////
        CSR_LPSTART0: csr_rdata_int = !COREV_PULP ? 'b0 : hwlp_start_i[0];  // Loop 0 start address
        CSR_LPEND0:   csr_rdata_int = !COREV_PULP ? 'b0 : hwlp_end_i[0];    // Loop 0 end address
        CSR_LPCOUNT0: csr_rdata_int = !COREV_PULP ? 'b0 : hwlp_cnt_i[0];    // Loop 0 counter
        CSR_LPSTART1: csr_rdata_int = !COREV_PULP ? 'b0 : hwlp_start_i[1];  // Loop 1 start address
        CSR_LPEND1:   csr_rdata_int = !COREV_PULP ? 'b0 : hwlp_end_i[1];    // Loop 1 end address
        CSR_LPCOUNT1: csr_rdata_int = !COREV_PULP ? 'b0 : hwlp_cnt_i[1];    // Loop 1 counter

        ///////////////////////////////////////////////////////////////////
        // PHYSICAL MEMORY PROTECTION (USE_PMP=1)
        ///////////////////////////////////////////////////////////////////
        // PMP configuration registers (4 bytes each, 4 PMP entries per register)
        CSR_PMPCFG0: csr_rdata_int = USE_PMP ? pmp_reg_q.pmpcfg_packed[0] : '0;
        CSR_PMPCFG1: csr_rdata_int = USE_PMP ? pmp_reg_q.pmpcfg_packed[1] : '0;
        CSR_PMPCFG2: csr_rdata_int = USE_PMP ? pmp_reg_q.pmpcfg_packed[2] : '0;
        CSR_PMPCFG3: csr_rdata_int = USE_PMP ? pmp_reg_q.pmpcfg_packed[3] : '0;

        // PMP address registers (16 entries)
        CSR_PMPADDR0, CSR_PMPADDR1, CSR_PMPADDR2, CSR_PMPADDR3,
      CSR_PMPADDR4, CSR_PMPADDR5, CSR_PMPADDR6, CSR_PMPADDR7,
      CSR_PMPADDR8, CSR_PMPADDR9, CSR_PMPADDR10, CSR_PMPADDR11,
      CSR_PMPADDR12, CSR_PMPADDR13, CSR_PMPADDR14, CSR_PMPADDR15 :
        csr_rdata_int = USE_PMP ? pmp_reg_q.pmpaddr[csr_addr_i[3:0]] : '0;

        ///////////////////////////////////////////////////////////////////
        // USER MODE CSRs (PULP_SECURE=1)
        ///////////////////////////////////////////////////////////////////
        // ustatus: User status register (subset of mstatus)
        CSR_USTATUS: csr_rdata_int = {27'b0, mstatus_q.upie, 3'h0, mstatus_q.uie};
        
        // utvec: User trap-handler base address
        CSR_UTVEC: csr_rdata_int = {utvec_q, 6'h0, utvec_mode_q};
        
        // uhartid: Hardware thread ID (duplicated for U-mode, non-standard)
        CSR_UHARTID: csr_rdata_int = !COREV_PULP ? 'b0 : hart_id_i;
        
        // uepc: User exception program counter
        CSR_UEPC: csr_rdata_int = uepc_q;
        
        // ucause: User exception cause
        CSR_UCAUSE: csr_rdata_int = {ucause_q[5], 26'h0, ucause_q[4:0]};

        ///////////////////////////////////////////////////////////////////
        // CUSTOM CSRs (non-standard)
        ///////////////////////////////////////////////////////////////////
        // privlv: Current privilege level (for software read, non-standard)
        CSR_PRIVLV: csr_rdata_int = !COREV_PULP ? 'b0 : {30'h0, priv_lvl_q};

        default: csr_rdata_int = '0;  // Unimplemented CSRs read as 0
      endcase
    end
  end else begin : gen_no_pulp_secure_read_logic  
    ///////////////////////////////////////////////////////////////////////////
    // CSR READ LOGIC (PULP_SECURE=0, M-mode only)
    ///////////////////////////////////////////////////////////////////////////
    // Simplified read logic without U-mode CSRs
    
    always_comb begin

      case (csr_addr_i)
        ///////////////////////////////////////////////////////////////////
        // FLOATING-POINT CSRs (FPU=1)
        ///////////////////////////////////////////////////////////////////
        CSR_FFLAGS: csr_rdata_int = (FPU == 1) ? {27'b0, fflags_q} : '0;
        CSR_FRM: csr_rdata_int = (FPU == 1) ? {29'b0, frm_q} : '0;
        CSR_FCSR: csr_rdata_int = (FPU == 1) ? {24'b0, frm_q, fflags_q} : '0;
        
        ///////////////////////////////////////////////////////////////////
        // MACHINE MODE CSRs
        ///////////////////////////////////////////////////////////////////
        // mstatus: Machine status (includes FP status when FPU enabled)
        CSR_MSTATUS:
        csr_rdata_int = {
          (FPU == 1 && ZFINX == 0) ? (mstatus_fs_q == FS_DIRTY ? 1'b1 : 1'b0) : 1'b0,  // SD bit
          13'b0,
          mstatus_q.mprv,           // [17] Modify privilege
          2'b0,
          (FPU == 1 && ZFINX == 0) ? mstatus_fs_q : FS_OFF,  // [14:13] FP status
          mstatus_q.mpp,            // [12:11] Previous privilege
          3'b0,
          mstatus_q.mpie,           // [7] Previous M-mode IE
          2'h0,
          mstatus_q.upie,           // [4] Previous U-mode IE
          mstatus_q.mie,            // [3] M-mode interrupt enable
          2'h0,
          mstatus_q.uie             // [0] U-mode interrupt enable
        };
        
        // misa: Machine ISA register
        CSR_MISA: csr_rdata_int = MISA_VALUE;
        
        // mie: Machine interrupt enable
        CSR_MIE: begin
          csr_rdata_int = mie_q;
        end

        // mtvec: Machine trap-handler base address
        CSR_MTVEC: csr_rdata_int = {mtvec_q, 6'h0, mtvec_mode_q};
        
        // mscratch: Machine scratch
        CSR_MSCRATCH: csr_rdata_int = mscratch_q;
        
        // mepc: Machine exception program counter
        CSR_MEPC: csr_rdata_int = mepc_q;
        
        // mcause: Machine exception cause
        CSR_MCAUSE: csr_rdata_int = {mcause_q[5], 26'b0, mcause_q[4:0]};
        
        // mip: Machine interrupt pending
        CSR_MIP: begin
          csr_rdata_int = mip;
        end
        
        ///////////////////////////////////////////////////////////////////
        // MACHINE INFORMATION CSRs
        ///////////////////////////////////////////////////////////////////
        CSR_MHARTID: csr_rdata_int = hart_id_i;  // Hardware thread ID
        CSR_MVENDORID: csr_rdata_int = {MVENDORID_BANK, MVENDORID_OFFSET};  // Vendor ID
        CSR_MARCHID: csr_rdata_int = MARCHID;    // Architecture ID

        // mimpid: Implementation ID (indicates FPU/PULP extensions)
        CSR_MIMPID: begin
          csr_rdata_int = (FPU == 1 || COREV_PULP == 1 || COREV_CLUSTER == 1) ? 32'h1 : 'b0;
        end

        // Unimplemented CSRs
        CSR_MTVAL: csr_rdata_int = 'b0;

        ///////////////////////////////////////////////////////////////////
        // DEBUG/TRIGGER CSRs
        ///////////////////////////////////////////////////////////////////
        CSR_TSELECT, CSR_TDATA3, CSR_MCONTEXT, CSR_SCONTEXT: csr_rdata_int = 'b0;
        CSR_TDATA1: csr_rdata_int = tmatch_control_rdata;
        CSR_TDATA2: csr_rdata_int = tmatch_value_rdata;
        CSR_TINFO: csr_rdata_int = tinfo_types;

        CSR_DCSR: csr_rdata_int = dcsr_q;
        CSR_DPC: csr_rdata_int = depc_q;
        CSR_DSCRATCH0: csr_rdata_int = dscratch0_q;
        CSR_DSCRATCH1: csr_rdata_int = dscratch1_q;

        ///////////////////////////////////////////////////////////////////
        // PERFORMANCE COUNTERS (lower 32 bits)
        ///////////////////////////////////////////////////////////////////
        CSR_MCYCLE,
      CSR_MINSTRET,
      CSR_MHPMCOUNTER3,
      CSR_MHPMCOUNTER4,  CSR_MHPMCOUNTER5,  CSR_MHPMCOUNTER6,  CSR_MHPMCOUNTER7,
      CSR_MHPMCOUNTER8,  CSR_MHPMCOUNTER9,  CSR_MHPMCOUNTER10, CSR_MHPMCOUNTER11,
      CSR_MHPMCOUNTER12, CSR_MHPMCOUNTER13, CSR_MHPMCOUNTER14, CSR_MHPMCOUNTER15,
      CSR_MHPMCOUNTER16, CSR_MHPMCOUNTER17, CSR_MHPMCOUNTER18, CSR_MHPMCOUNTER19,
      CSR_MHPMCOUNTER20, CSR_MHPMCOUNTER21, CSR_MHPMCOUNTER22, CSR_MHPMCOUNTER23,
      CSR_MHPMCOUNTER24, CSR_MHPMCOUNTER25, CSR_MHPMCOUNTER26, CSR_MHPMCOUNTER27,
      CSR_MHPMCOUNTER28, CSR_MHPMCOUNTER29, CSR_MHPMCOUNTER30, CSR_MHPMCOUNTER31,
      CSR_CYCLE,        // U-mode alias for mcycle
      CSR_INSTRET,      // U-mode alias for minstret
      CSR_HPMCOUNTER3,  // U-mode aliases for mhpmcounters (accessible if PULP_SECURE=1)
      CSR_HPMCOUNTER4,  CSR_HPMCOUNTER5,  CSR_HPMCOUNTER6,  CSR_HPMCOUNTER7,
      CSR_HPMCOUNTER8,  CSR_HPMCOUNTER9,  CSR_HPMCOUNTER10, CSR_HPMCOUNTER11,
      CSR_HPMCOUNTER12, CSR_HPMCOUNTER13, CSR_HPMCOUNTER14, CSR_HPMCOUNTER15,
      CSR_HPMCOUNTER16, CSR_HPMCOUNTER17, CSR_HPMCOUNTER18, CSR_HPMCOUNTER19,
      CSR_HPMCOUNTER20, CSR_HPMCOUNTER21, CSR_HPMCOUNTER22, CSR_HPMCOUNTER23,
      CSR_HPMCOUNTER24, CSR_HPMCOUNTER25, CSR_HPMCOUNTER26, CSR_HPMCOUNTER27,
      CSR_HPMCOUNTER28, CSR_HPMCOUNTER29, CSR_HPMCOUNTER30, CSR_HPMCOUNTER31:
        csr_rdata_int = mhpmcounter_q[csr_addr_i[4:0]][31:0];  // Lower 32 bits

        ///////////////////////////////////////////////////////////////////
        // PERFORMANCE COUNTERS (upper 32 bits)
        ///////////////////////////////////////////////////////////////////
        CSR_MCYCLEH,
      CSR_MINSTRETH,
      CSR_MHPMCOUNTER3H,
      CSR_MHPMCOUNTER4H,  CSR_MHPMCOUNTER5H,  CSR_MHPMCOUNTER6H,  CSR_MHPMCOUNTER7H,
      CSR_MHPMCOUNTER8H,  CSR_MHPMCOUNTER9H,  CSR_MHPMCOUNTER10H, CSR_MHPMCOUNTER11H,
      CSR_MHPMCOUNTER12H, CSR_MHPMCOUNTER13H, CSR_MHPMCOUNTER14H, CSR_MHPMCOUNTER15H,
      CSR_MHPMCOUNTER16H, CSR_MHPMCOUNTER17H, CSR_MHPMCOUNTER18H, CSR_MHPMCOUNTER19H,
      CSR_MHPMCOUNTER20H, CSR_MHPMCOUNTER21H, CSR_MHPMCOUNTER22H, CSR_MHPMCOUNTER23H,
      CSR_MHPMCOUNTER24H, CSR_MHPMCOUNTER25H, CSR_MHPMCOUNTER26H, CSR_MHPMCOUNTER27H,
      CSR_MHPMCOUNTER28H, CSR_MHPMCOUNTER29H, CSR_MHPMCOUNTER30H, CSR_MHPMCOUNTER31H,
      CSR_CYCLEH,         // U-mode alias for mcycleh
      CSR_INSTRETH,       // U-mode alias for minstreth
      CSR_HPMCOUNTER3H,   // U-mode aliases for upper 32 bits
      CSR_HPMCOUNTER4H,  CSR_HPMCOUNTER5H,  CSR_HPMCOUNTER6H,  CSR_HPMCOUNTER7H,
      CSR_HPMCOUNTER8H,  CSR_HPMCOUNTER9H,  CSR_HPMCOUNTER10H, CSR_HPMCOUNTER11H,
      CSR_HPMCOUNTER12H, CSR_HPMCOUNTER13H, CSR_HPMCOUNTER14H, CSR_HPMCOUNTER15H,
      CSR_HPMCOUNTER16H, CSR_HPMCOUNTER17H, CSR_HPMCOUNTER18H, CSR_HPMCOUNTER19H,
      CSR_HPMCOUNTER20H, CSR_HPMCOUNTER21H, CSR_HPMCOUNTER22H, CSR_HPMCOUNTER23H,
      CSR_HPMCOUNTER24H, CSR_HPMCOUNTER25H, CSR_HPMCOUNTER26H, CSR_HPMCOUNTER27H,
      CSR_HPMCOUNTER28H, CSR_HPMCOUNTER29H, CSR_HPMCOUNTER30H, CSR_HPMCOUNTER31H:
        csr_rdata_int = (MHPMCOUNTER_WIDTH == 64) ? mhpmcounter_q[csr_addr_i[4:0]][63:32] : '0;

        ///////////////////////////////////////////////////////////////////
        // PERFORMANCE COUNTER CONTROL CSRs
        ///////////////////////////////////////////////////////////////////
        CSR_MCOUNTINHIBIT: csr_rdata_int = mcountinhibit_q;  // Counter inhibit

        // Performance event selectors
        CSR_MHPMEVENT3,
      CSR_MHPMEVENT4,  CSR_MHPMEVENT5,  CSR_MHPMEVENT6,  CSR_MHPMEVENT7,
      CSR_MHPMEVENT8,  CSR_MHPMEVENT9,  CSR_MHPMEVENT10, CSR_MHPMEVENT11,
      CSR_MHPMEVENT12, CSR_MHPMEVENT13, CSR_MHPMEVENT14, CSR_MHPMEVENT15,
      CSR_MHPMEVENT16, CSR_MHPMEVENT17, CSR_MHPMEVENT18, CSR_MHPMEVENT19,
      CSR_MHPMEVENT20, CSR_MHPMEVENT21, CSR_MHPMEVENT22, CSR_MHPMEVENT23,
      CSR_MHPMEVENT24, CSR_MHPMEVENT25, CSR_MHPMEVENT26, CSR_MHPMEVENT27,
      CSR_MHPMEVENT28, CSR_MHPMEVENT29, CSR_MHPMEVENT30, CSR_MHPMEVENT31:
        csr_rdata_int = mhpmevent_q[csr_addr_i[4:0]];

        ///////////////////////////////////////////////////////////////////
        // HARDWARE LOOP CSRs (COREV_PULP=1, non-standard)
        ///////////////////////////////////////////////////////////////////
        CSR_LPSTART0: csr_rdata_int = !COREV_PULP ? 'b0 : hwlp_start_i[0];
        CSR_LPEND0:   csr_rdata_int = !COREV_PULP ? 'b0 : hwlp_end_i[0];
        CSR_LPCOUNT0: csr_rdata_int = !COREV_PULP ? 'b0 : hwlp_cnt_i[0];
        CSR_LPSTART1: csr_rdata_int = !COREV_PULP ? 'b0 : hwlp_start_i[1];
        CSR_LPEND1:   csr_rdata_int = !COREV_PULP ? 'b0 : hwlp_end_i[1];
        CSR_LPCOUNT1: csr_rdata_int = !COREV_PULP ? 'b0 : hwlp_cnt_i[1];

        ///////////////////////////////////////////////////////////////////
        // CUSTOM CSRs (non-standard, COREV_PULP extensions)
        ///////////////////////////////////////////////////////////////////
        CSR_UHARTID: csr_rdata_int = !COREV_PULP ? 'b0 : hart_id_i;       // Duplicated for U-mode
        CSR_PRIVLV: csr_rdata_int = !COREV_PULP ? 'b0 : {30'h0, priv_lvl_q};  // Current privilege level
        CSR_ZFINX: csr_rdata_int = (FPU == 1 && ZFINX == 1) ? 32'h1 : 32'h0;  // Zfinx extension indicator

        default: csr_rdata_int = '0;  // Unimplemented CSRs read as 0
      endcase
    end
  end  //PULP_SECURE

  ///////////////////////////////////////////////////////////////////////////
  // CSR WRITE LOGIC (PULP_SECURE=1, with U-mode support)
  ///////////////////////////////////////////////////////////////////////////
  // Handles CSR write operations and automatic updates on exceptions/interrupts
  
  if (PULP_SECURE == 1) begin : gen_pulp_secure_write_logic
    always_comb begin
      // Default: Hold all CSR values unless explicitly updated
      fflags_n                = fflags_q;
      frm_n                   = frm_q;
      mscratch_n              = mscratch_q;
      mepc_n                  = mepc_q;
      uepc_n                  = uepc_q;
      depc_n                  = depc_q;
      dcsr_n                  = dcsr_q;
      dscratch0_n             = dscratch0_q;
      dscratch1_n             = dscratch1_q;

      mstatus_n               = mstatus_q;
      mcause_n                = mcause_q;
      ucause_n                = ucause_q;
      exception_pc            = pc_id_i;
      priv_lvl_n              = priv_lvl_q;
      mtvec_n                 = csr_mtvec_init_i ? mtvec_addr_i[31:8] : mtvec_q;  // Boot-time init or hold
      utvec_n                 = utvec_q;
      mtvec_mode_n            = mtvec_mode_q;
      utvec_mode_n            = utvec_mode_q;
      pmp_reg_n.pmpaddr       = pmp_reg_q.pmpaddr;
      pmp_reg_n.pmpcfg_packed = pmp_reg_q.pmpcfg_packed;
      pmpaddr_we              = '0;  // Clock gating control
      pmpcfg_we               = '0;  // Clock gating control

      mie_n                   = mie_q;

      // Automatic fflags update: OR-in new flags on FP instruction completion
      if (FPU == 1) if (fflags_we_i) fflags_n = fflags_i | fflags_q;

      ///////////////////////////////////////////////////////////////////
      // CSR WRITE CASE STATEMENT
      ///////////////////////////////////////////////////////////////////
      case (csr_addr_i)
        ///////////////////////////////////////////////////////////////////
        // FLOATING-POINT CSRs (FPU=1)
        ///////////////////////////////////////////////////////////////////
        CSR_FFLAGS: if (csr_we_int) fflags_n = (FPU == 1) ? csr_wdata_int[C_FFLAG-1:0] : '0;
        CSR_FRM:    if (csr_we_int) frm_n = (FPU == 1) ? csr_wdata_int[C_RM-1:0] : '0;
        CSR_FCSR:   // Combined fcsr write updates both frm and fflags
        if (csr_we_int) begin
          fflags_n = (FPU == 1) ? csr_wdata_int[C_FFLAG-1:0] : '0;
          frm_n    = (FPU == 1) ? csr_wdata_int[C_RM+C_FFLAG-1:C_FFLAG] : '0;
        end

        ///////////////////////////////////////////////////////////////////
        // MACHINE MODE CSRs
        ///////////////////////////////////////////////////////////////////
        // mstatus: Machine status (write only subset of fields, not full 32-bit)
        CSR_MSTATUS:
        if (csr_we_int) begin
          mstatus_n = '{
              uie: csr_wdata_int[MSTATUS_UIE_BIT],           // [0] U-mode interrupt enable
              mie: csr_wdata_int[MSTATUS_MIE_BIT],           // [3] M-mode interrupt enable
              upie: csr_wdata_int[MSTATUS_UPIE_BIT],         // [4] Previous U-mode IE
              mpie: csr_wdata_int[MSTATUS_MPIE_BIT],         // [7] Previous M-mode IE
              mpp: PrivLvl_t'(csr_wdata_int[MSTATUS_MPP_BIT_HIGH:MSTATUS_MPP_BIT_LOW]),  // [12:11] Previous privilege
              mprv: csr_wdata_int[MSTATUS_MPRV_BIT]          // [17] Modify privilege for loads/stores
          };
        end
        
        // mie: Machine interrupt enable (masked to valid IRQ bits)
        CSR_MIE:
        if (csr_we_int) begin
          mie_n = csr_wdata_int & IRQ_MASK;  // Only write implemented interrupt bits
        end
        
        // mtvec: Machine trap-handler base address
        CSR_MTVEC:
        if (csr_we_int) begin
          mtvec_n      = csr_wdata_int[31:8];                // Base address (256-byte aligned)
          mtvec_mode_n = {1'b0, csr_wdata_int[0]};           // Mode: 0=direct, 1=vectored
        end
        
        // mscratch: Machine scratch register (for trap handler use)
        CSR_MSCRATCH:
        if (csr_we_int) begin
          mscratch_n = csr_wdata_int;
        end
        
        // mepc: Machine exception program counter (16-bit aligned)
        CSR_MEPC:
        if (csr_we_int) begin
          mepc_n = csr_wdata_int & ~32'b1;  // Force 16-bit alignment (clear bit 0)
        end
        
        // mcause: Machine exception cause (interrupt bit + exception code)
        CSR_MCAUSE: if (csr_we_int) mcause_n = {csr_wdata_int[31], csr_wdata_int[4:0]};

        ///////////////////////////////////////////////////////////////////
        // DEBUG CSRs
        ///////////////////////////////////////////////////////////////////
        // dcsr: Debug control and status register
        CSR_DCSR:
        if (csr_we_int) begin
          // Read-only fields (not assigned here, dcsr_q value preserved):
          // - xdebugver: Debug spec version
          // - cause: Debug entry cause
          // - nmip: Non-maskable interrupt pending
          
          dcsr_n.ebreakm = csr_wdata_int[15];    // M-mode EBREAK enters debug
          dcsr_n.ebreaks = 1'b0;                 // S-mode EBREAK (WARL, reads 0)
          dcsr_n.ebreaku = csr_wdata_int[12];    // U-mode EBREAK enters debug
          dcsr_n.stepie = csr_wdata_int[11];     // Interrupts enabled during single-step
          dcsr_n.stopcount = 1'b0;               // Stop counters in debug (WARL, reads 0)
          dcsr_n.stoptime = 1'b0;                // Stop time in debug (WARL, reads 0)
          dcsr_n.mprven = 1'b0;                  // MPRV in debug (WARL, reads 0)
          dcsr_n.step = csr_wdata_int[2];        // Single-step mode enable
          dcsr_n.prv = (PrivLvl_t'(csr_wdata_int[1:0]) == PRIV_LVL_M) ? PRIV_LVL_M : PRIV_LVL_U;  // Privilege on dret (WARL)
        end

        // dpc: Debug program counter (16-bit aligned)
        CSR_DPC:
        if (csr_we_int) begin
          depc_n = csr_wdata_int & ~32'b1;  // Force 16-bit alignment
        end

        // dscratch0/1: Debug scratch registers
        CSR_DSCRATCH0:
        if (csr_we_int) begin
          dscratch0_n = csr_wdata_int;
        end

        CSR_DSCRATCH1:
        if (csr_we_int) begin
          dscratch1_n = csr_wdata_int;
        end

        ///////////////////////////////////////////////////////////////////
        // PHYSICAL MEMORY PROTECTION CSRs
        ///////////////////////////////////////////////////////////////////
        // pmpcfg: Configuration registers (4 entries each, 4 registers total)
        CSR_PMPCFG0:
        if (csr_we_int) begin
          pmp_reg_n.pmpcfg_packed[0] = csr_wdata_int;
          pmpcfg_we[3:0] = 4'b1111;  // Clock gating control for entries 0-3
        end
        CSR_PMPCFG1:
        if (csr_we_int) begin
          pmp_reg_n.pmpcfg_packed[1] = csr_wdata_int;
          pmpcfg_we[7:4] = 4'b1111;  // Entries 4-7
        end
        CSR_PMPCFG2:
        if (csr_we_int) begin
          pmp_reg_n.pmpcfg_packed[2] = csr_wdata_int;
          pmpcfg_we[11:8] = 4'b1111;  // Entries 8-11
        end
        CSR_PMPCFG3:
        if (csr_we_int) begin
          pmp_reg_n.pmpcfg_packed[3] = csr_wdata_int;
          pmpcfg_we[15:12] = 4'b1111;  // Entries 12-15
        end

        // pmpaddr: Address registers (16 entries)
        CSR_PMPADDR0, CSR_PMPADDR1, CSR_PMPADDR2, CSR_PMPADDR3,
      CSR_PMPADDR4, CSR_PMPADDR5, CSR_PMPADDR6, CSR_PMPADDR7,
      CSR_PMPADDR8, CSR_PMPADDR9, CSR_PMPADDR10, CSR_PMPADDR11,
      CSR_PMPADDR12, CSR_PMPADDR13, CSR_PMPADDR14, CSR_PMPADDR15 :
        if (csr_we_int) begin
          pmp_reg_n.pmpaddr[csr_addr_i[3:0]] = csr_wdata_int;
          pmpaddr_we[csr_addr_i[3:0]] = 1'b1;  // Clock gating control
        end

        ///////////////////////////////////////////////////////////////////
        // USER MODE CSRs (PULP_SECURE=1)
        ///////////////////////////////////////////////////////////////////
        // ustatus: User status (subset of mstatus)
        CSR_USTATUS:
        if (csr_we_int) begin
          mstatus_n = '{
              uie: csr_wdata_int[MSTATUS_UIE_BIT],   // [0] U-mode interrupt enable
              mie: mstatus_q.mie,                    // Preserve M-mode IE
              upie: csr_wdata_int[MSTATUS_UPIE_BIT], // [4] Previous U-mode IE
              mpie: mstatus_q.mpie,                  // Preserve previous M-mode IE
              mpp: mstatus_q.mpp,                    // Preserve previous privilege
              mprv: mstatus_q.mprv                   // Preserve MPRV
          };
        end
        
        // utvec: User trap-handler base address
        CSR_UTVEC:
        if (csr_we_int) begin
          utvec_n      = csr_wdata_int[31:8];
          utvec_mode_n = {1'b0, csr_wdata_int[0]};  // Mode: 0=direct, 1=vectored
        end
        
        // uepc: User exception program counter
        CSR_UEPC:
        if (csr_we_int) begin
          uepc_n = csr_wdata_int;
        end
        
        // ucause: User exception cause
        CSR_UCAUSE: if (csr_we_int) ucause_n = {csr_wdata_int[31], csr_wdata_int[4:0]};
      endcase

      ///////////////////////////////////////////////////////////////////
      // EXCEPTION/INTERRUPT HANDLING (overrides CSR writes)
      ///////////////////////////////////////////////////////////////////
      // Exception controller has priority over explicit CSR writes
      
      unique case (1'b1)

        csr_save_cause_i: begin  // Exception or interrupt occurred

          // Determine exception PC source based on pipeline stage
          unique case (1'b1)
            csr_save_if_i: exception_pc = pc_if_i;  // Exception in IF stage
            csr_save_id_i: exception_pc = pc_id_i;  // Exception in ID stage
            csr_save_ex_i: exception_pc = pc_ex_i;  // Exception in EX stage
            default: ;
          endcase

          // Handle exception/interrupt based on current privilege level
          unique case (priv_lvl_q)

            PRIV_LVL_U: begin  // Currently in User mode
              if (~is_irq) begin
                // EXCEPTION from U-mode: Always trap to M-mode (Ecall, illegal inst, etc.)
                priv_lvl_n     = PRIV_LVL_M;
                mstatus_n.mpie = mstatus_q.uie;  // Save U-mode IE to MPIE
                mstatus_n.mie  = 1'b0;           // Disable M-mode interrupts
                mstatus_n.mpp  = PRIV_LVL_U;     // Save previous privilege (U)
                if (debug_csr_save_i) depc_n = exception_pc;  // Debug exception
                else mepc_n = exception_pc;      // Normal exception PC
                mcause_n = csr_cause_i;          // Exception cause code

              end else begin
                // INTERRUPT from U-mode: Delegate to U or M based on security
                if (~csr_irq_sec_i) begin
                  // SECURE INTERRUPT (U --> U): Delegate to U-mode handler
                  priv_lvl_n     = PRIV_LVL_U;
                  mstatus_n.upie = mstatus_q.uie;  // Save U-mode IE to UPIE
                  mstatus_n.uie  = 1'b0;           // Disable U-mode interrupts
                  if (debug_csr_save_i) depc_n = exception_pc;
                  else uepc_n = exception_pc;      // Save PC to uepc
                  ucause_n = csr_cause_i;          // Save cause to ucause

                end else begin
                  // NON-SECURE INTERRUPT (U --> M): Trap to M-mode
                  priv_lvl_n     = PRIV_LVL_M;
                  mstatus_n.mpie = mstatus_q.uie;  // Save U-mode IE to MPIE
                  mstatus_n.mie  = 1'b0;           // Disable M-mode interrupts
                  mstatus_n.mpp  = PRIV_LVL_U;     // Save previous privilege (U)
                  if (debug_csr_save_i) depc_n = exception_pc;
                  else mepc_n = exception_pc;
                  mcause_n = csr_cause_i;
                end
              end
            end  //PRIV_LVL_U

            PRIV_LVL_M: begin  // Currently in Machine mode
              if (debug_csr_save_i) begin
                // DEBUG EXCEPTION: Enter debug mode (all interrupts masked)
                dcsr_n.prv   = PRIV_LVL_M;      // Save privilege level
                dcsr_n.cause = debug_cause_i;   // Debug entry cause
                depc_n       = exception_pc;    // Save PC to dpc
              end else begin
                // EXCEPTION/INTERRUPT from M-mode: Always M --> M
                priv_lvl_n     = PRIV_LVL_M;
                mstatus_n.mpie = mstatus_q.mie;  // Save M-mode IE to MPIE
                mstatus_n.mie  = 1'b0;           // Disable M-mode interrupts
                mstatus_n.mpp  = PRIV_LVL_M;     // Save previous privilege (M)
                mepc_n         = exception_pc;
                mcause_n       = csr_cause_i;
              end
            end  //PRIV_LVL_M
            default: ;

          endcase

        end  //csr_save_cause_i

        ///////////////////////////////////////////////////////////////////
        // EXCEPTION RETURN INSTRUCTIONS
        ///////////////////////////////////////////////////////////////////
        
        csr_restore_uret_i: begin  // URET: Return from U-mode trap handler
          mstatus_n.uie  = mstatus_q.upie;  // Restore U-mode IE from UPIE
          priv_lvl_n     = PRIV_LVL_U;      // Return to U-mode
          mstatus_n.upie = 1'b1;            // Set UPIE to 1
        end  //csr_restore_uret_i

        csr_restore_mret_i: begin  // MRET: Return from M-mode trap handler
          // Restore privilege level and interrupt enable based on MPP
          unique case (mstatus_q.mpp)
            PRIV_LVL_U: begin
              mstatus_n.uie  = mstatus_q.mpie;  // Restore U-mode IE
              priv_lvl_n     = PRIV_LVL_U;      // Return to U-mode
              mstatus_n.mpie = 1'b1;            // Set MPIE to 1
              mstatus_n.mpp  = PRIV_LVL_U;      // Set MPP to U
            end
            PRIV_LVL_M: begin
              mstatus_n.mie  = mstatus_q.mpie;  // Restore M-mode IE
              priv_lvl_n     = PRIV_LVL_M;      // Return to M-mode
              mstatus_n.mpie = 1'b1;            // Set MPIE to 1
              mstatus_n.mpp  = PRIV_LVL_U;
            end
            default: ;
          endcase
        end  //csr_restore_mret_i


        csr_restore_dret_i: begin  // DRET: Return from Debug mode
          priv_lvl_n = dcsr_q.prv;  // Restore privilege level from dcsr.prv
        end  //csr_restore_dret_i

        default: ;
      endcase
    end
  end else begin : gen_no_pulp_secure_write_logic
    ///////////////////////////////////////////////////////////////////////////
    // CSR WRITE LOGIC (PULP_SECURE=0, M-mode only)
    ///////////////////////////////////////////////////////////////////////////
    // Simplified write logic without U-mode support
    
    always_comb begin
      if (FPU == 1) begin
        fflags_n = fflags_q;
        frm_n = frm_q;
        if (ZFINX == 0) begin
          mstatus_fs_n = mstatus_fs_q;
          fcsr_update  = 1'b0;
        end
      end
      mscratch_n = mscratch_q;
      mepc_n = mepc_q;
      uepc_n = 'b0;  // Not used if PULP_SECURE == 0
      depc_n = depc_q;
      dcsr_n = dcsr_q;
      dscratch0_n = dscratch0_q;
      dscratch1_n = dscratch1_q;

      mstatus_we_int = 1'b0;
      mstatus_n = mstatus_q;
      mcause_n = mcause_q;
      ucause_n = '0;  // Not used if PULP_SECURE == 0
      exception_pc = pc_id_i;
      priv_lvl_n = priv_lvl_q;
      mtvec_n = csr_mtvec_init_i ? mtvec_addr_i[31:8] : mtvec_q;
      utvec_n = '0;  // Not used if PULP_SECURE == 0
      pmp_reg_n.pmpaddr = '0;  // Not used if PULP_SECURE == 0
      pmp_reg_n.pmpcfg_packed = '0;  // Not used if PULP_SECURE == 0
      pmp_reg_n.pmpcfg = '0;  // Not used if PULP_SECURE == 0
      pmpaddr_we = '0;
      pmpcfg_we = '0;

      mie_n = mie_q;
      mtvec_mode_n = mtvec_mode_q;
      utvec_mode_n = '0;  // Not used if PULP_SECURE == 0

      case (csr_addr_i)
        // fcsr: Floating-Point Control and Status Register (frm, fflags, fprec).
        CSR_FFLAGS:
        if (FPU == 1) begin
          if (csr_we_int) begin
            fflags_n = csr_wdata_int[C_FFLAG-1:0];
            if (ZFINX == 0) begin
              fcsr_update = 1'b1;
            end
          end
        end
        CSR_FRM:
        if (FPU == 1) begin
          if (csr_we_int) begin
            frm_n = csr_wdata_int[C_RM-1:0];
            if (ZFINX == 0) begin
              fcsr_update = 1'b1;
            end
          end
        end
        CSR_FCSR:
        if (FPU == 1) begin
          if (csr_we_int) begin
            fflags_n = csr_wdata_int[C_FFLAG-1:0];
            frm_n    = csr_wdata_int[C_RM+C_FFLAG-1:C_FFLAG];
            if (ZFINX == 0) begin
              fcsr_update = 1'b1;
            end
          end
        end

        // mstatus
        CSR_MSTATUS:
        if (csr_we_int) begin
          mstatus_n = '{
              uie: csr_wdata_int[MSTATUS_UIE_BIT],
              mie: csr_wdata_int[MSTATUS_MIE_BIT],
              upie: csr_wdata_int[MSTATUS_UPIE_BIT],
              mpie: csr_wdata_int[MSTATUS_MPIE_BIT],
              mpp: PrivLvl_t'(csr_wdata_int[MSTATUS_MPP_BIT_HIGH:MSTATUS_MPP_BIT_LOW]),
              mprv: csr_wdata_int[MSTATUS_MPRV_BIT]
          };
          if (FPU == 1 && ZFINX == 0) begin
            mstatus_we_int = 1'b1;
            mstatus_fs_n   = FS_t'(csr_wdata_int[MSTATUS_FS_BIT_HIGH:MSTATUS_FS_BIT_LOW]);
          end
        end
        // mie: machine interrupt enable
        CSR_MIE:
        if (csr_we_int) begin
          mie_n = csr_wdata_int & IRQ_MASK;
        end
        // mtvec: machine trap-handler base address
        CSR_MTVEC:
        if (csr_we_int) begin
          mtvec_n      = csr_wdata_int[31:8];
          mtvec_mode_n = {1'b0, csr_wdata_int[0]};  // Only direct and vectored mode are supported
        end
        // mscratch: machine scratch
        CSR_MSCRATCH:
        if (csr_we_int) begin
          mscratch_n = csr_wdata_int;
        end
        // mepc: exception program counter
        CSR_MEPC:
        if (csr_we_int) begin
          mepc_n = csr_wdata_int & ~32'b1;  // force 16-bit alignment
        end
        // mcause
        CSR_MCAUSE: if (csr_we_int) mcause_n = {csr_wdata_int[31], csr_wdata_int[4:0]};

        CSR_DCSR:
        if (csr_we_int) begin
          // Following are read-only and never assigned here (dcsr_q value is used):
          //
          // - xdebugver
          // - cause
          // - nmip

          dcsr_n.ebreakm   = csr_wdata_int[15];
          dcsr_n.ebreaks   = 1'b0;  // ebreaks (implemented as WARL)
          dcsr_n.ebreaku   = 1'b0;  // ebreaku (implemented as WARL)
          dcsr_n.stepie    = csr_wdata_int[11];  // stepie
          dcsr_n.stopcount = 1'b0;  // stopcount
          dcsr_n.stoptime  = 1'b0;  // stoptime
          dcsr_n.mprven    = 1'b0;  // mprven
          dcsr_n.step      = csr_wdata_int[2];
          dcsr_n.prv       = PRIV_LVL_M;  // prv (implemendted as WARL)
        end

        CSR_DPC:
        if (csr_we_int) begin
          depc_n = csr_wdata_int & ~32'b1;  // force 16-bit alignment
        end

        CSR_DSCRATCH0:
        if (csr_we_int) begin
          dscratch0_n = csr_wdata_int;
        end

        CSR_DSCRATCH1:
        if (csr_we_int) begin
          dscratch1_n = csr_wdata_int;
        end

      endcase

      // Automatic FPU status tracking (FPU=1, ZFINX=0)
      if (FPU == 1) begin
        // Auto-update fflags: OR-in new flags on FP instruction completion
        if (fflags_we_i) begin
          fflags_n = fflags_i | fflags_q;
        end

        if (ZFINX == 0) begin
          // FPU Register File/Flags implicit update: mark mstatus.FS as DIRTY
          // when FP registers are modified or fflags are set
          if ((fregs_we_i && !(mstatus_we_int && mstatus_fs_n != FS_DIRTY)) || fflags_we_i || fcsr_update) begin
            mstatus_fs_n = FS_DIRTY;  // FPU state modified
          end
        end
      end

      ///////////////////////////////////////////////////////////////////
      // EXCEPTION/INTERRUPT HANDLING (overrides CSR writes, M-mode only)
      ///////////////////////////////////////////////////////////////////
      unique case (1'b1)

        csr_save_cause_i: begin  // Exception or interrupt occurred
          // Determine exception PC source
          unique case (1'b1)
            csr_save_if_i: exception_pc = pc_if_i;
            csr_save_id_i: exception_pc = pc_id_i;
            csr_save_ex_i: exception_pc = pc_ex_i;
            default: ;
          endcase

          if (debug_csr_save_i) begin
            // DEBUG EXCEPTION: Enter debug mode
            dcsr_n.prv   = PRIV_LVL_M;      // Save privilege level
            dcsr_n.cause = debug_cause_i;   // Debug entry cause
            depc_n       = exception_pc;    // Save PC to dpc
          end else begin
            // EXCEPTION/INTERRUPT: Always M --> M (no U-mode support)
            priv_lvl_n     = PRIV_LVL_M;
            mstatus_n.mpie = mstatus_q.mie;  // Save M-mode IE to MPIE
            mstatus_n.mie  = 1'b0;           // Disable M-mode interrupts
            mstatus_n.mpp  = PRIV_LVL_M;     // Save previous privilege (M)
            mepc_n         = exception_pc;
            mcause_n       = csr_cause_i;
          end
        end  //csr_save_cause_i

        csr_restore_mret_i: begin  // MRET: Return from M-mode trap handler
          mstatus_n.mie  = mstatus_q.mpie;  // Restore M-mode IE from MPIE
          priv_lvl_n     = PRIV_LVL_M;      // Return to M-mode (only mode available)
          mstatus_n.mpie = 1'b1;            // Set MPIE to 1
          mstatus_n.mpp  = PRIV_LVL_M;      // Set MPP to M
        end  //csr_restore_mret_i

        csr_restore_dret_i: begin  // DRET: Return from Debug mode
          priv_lvl_n = dcsr_q.prv;  // Restore privilege level (always M)
        end  //csr_restore_dret_i

        default: ;
      endcase
    end
  end  //PULP_SECURE

  ///////////////////////////////////////////////////////////////////////////
  // CSR OPERATION DECODE
  ///////////////////////////////////////////////////////////////////////////
  // Decodes the CSR operation (CSRRW, CSRRS, CSRRC) and generates write data
  
  always_comb begin
    csr_wdata_int = csr_wdata_i;
    csr_we_int    = 1'b1;

    case (csr_op_i)
      CSR_OP_WRITE: csr_wdata_int = csr_wdata_i;                      // CSRRW: Write
      CSR_OP_SET:   csr_wdata_int = csr_wdata_i | csr_rdata_o;        // CSRRS: Set bits
      CSR_OP_CLEAR: csr_wdata_int = (~csr_wdata_int) & csr_rdata_o;   // CSRRC: Clear bits

      CSR_OP_READ: begin  // CSRR: Read only (no write)
        csr_wdata_int = csr_wdata_i;
        csr_we_int    = 1'b0;
      end
    endcase
  end

  ///////////////////////////////////////////////////////////////////////////
  // CSR OUTPUT ASSIGNMENTS
  ///////////////////////////////////////////////////////////////////////////
  
  assign csr_rdata_o = csr_rdata_int;  // CSR read data to ID stage

  // Interrupt enable outputs (masked by single-step mode)
  assign m_irq_enable_o = mstatus_q.mie && !(dcsr_q.step && !dcsr_q.stepie);
  assign u_irq_enable_o = mstatus_q.uie && !(dcsr_q.step && !dcsr_q.stepie);
  
  // Privilege level outputs
  assign priv_lvl_o = priv_lvl_q;      // Current privilege level (M or U)
  assign sec_lvl_o = priv_lvl_q[0];    // Security level (LSB of privilege)

  // FPU status outputs
  assign fs_off_o = (FPU == 1 && ZFINX == 0) ? (mstatus_fs_q == FS_OFF ? 1'b1 : 1'b0) : 1'b0;  // FPU disabled
  assign frm_o = (FPU == 1) ? frm_q : '0;  // FP rounding mode

  // Trap vector outputs
  assign mtvec_o = mtvec_q;
  assign utvec_o = utvec_q;
  assign mtvec_mode_o = mtvec_mode_q;
  assign utvec_mode_o = utvec_mode_q;

  assign mepc_o = mepc_q;
  assign uepc_o = uepc_q;

  assign mcounteren_o = PULP_SECURE ? mcounteren_q : '0;

  assign depc_o = depc_q;

  assign pmp_addr_o = pmp_reg_q.pmpaddr;
  assign pmp_cfg_o = pmp_reg_q.pmpcfg;

  assign debug_single_step_o = dcsr_q.step;
  assign debug_ebreakm_o = dcsr_q.ebreakm;
  assign debug_ebreaku_o = dcsr_q.ebreaku;

  generate
    if (PULP_SECURE == 1) begin : gen_pmp_user

      for (j = 0; j < N_PMP_ENTRIES; j++) begin : CS_PMP_CFG
        assign pmp_reg_n.pmpcfg[j] = pmp_reg_n.pmpcfg_packed[j/4][8*((j%4)+1)-1:8*(j%4)];
        assign pmp_reg_q.pmpcfg_packed[j/4][8*((j%4)+1)-1:8*(j%4)] = pmp_reg_q.pmpcfg[j];
      end

      for (j = 0; j < N_PMP_ENTRIES; j++) begin : CS_PMP_REGS_FF
        always_ff @(posedge clk, negedge rst_n) begin
          if (rst_n == 1'b0) begin
            pmp_reg_q.pmpcfg[j]  <= '0;
            pmp_reg_q.pmpaddr[j] <= '0;
          end else begin
            if (pmpcfg_we[j]) pmp_reg_q.pmpcfg[j] <= USE_PMP ? pmp_reg_n.pmpcfg[j] : '0;
            if (pmpaddr_we[j]) pmp_reg_q.pmpaddr[j] <= USE_PMP ? pmp_reg_n.pmpaddr[j] : '0;
          end
        end
      end  //CS_PMP_REGS_FF

      always_ff @(posedge clk, negedge rst_n) begin
        if (rst_n == 1'b0) begin
          uepc_q       <= '0;
          ucause_q     <= '0;
          utvec_q      <= '0;
          utvec_mode_q <= MTVEC_MODE;
          priv_lvl_q   <= PRIV_LVL_M;
        end else begin
          uepc_q       <= uepc_n;
          ucause_q     <= ucause_n;
          utvec_q      <= utvec_n;
          utvec_mode_q <= utvec_mode_n;
          priv_lvl_q   <= priv_lvl_n;
        end
      end
    end else begin : gen_no_pmp_user
      assign pmp_reg_q    = '0;
      assign uepc_q       = '0;
      assign ucause_q     = '0;
      assign utvec_q      = '0;
      assign utvec_mode_q = '0;
      assign priv_lvl_q   = PRIV_LVL_M;
    end
  endgenerate

  // actual registers
  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      if (FPU == 1) begin
        frm_q <= '0;
        fflags_q <= '0;
        if (ZFINX == 0) begin
          mstatus_fs_q <= FS_OFF;
        end
      end
      mstatus_q <= '{
          uie: 1'b0,
          mie: 1'b0,
          upie: 1'b0,
          mpie: 1'b0,
          mpp: PRIV_LVL_M,
          mprv: 1'b0
      };
      mepc_q <= '0;
      mcause_q <= '0;

      depc_q <= '0;
      dcsr_q <= '{
          xdebugver: XDEBUGVER_STD,
          cause: DBG_CAUSE_NONE,  // 3'h0
          prv: PRIV_LVL_M,
          default: '0
      };
      dscratch0_q <= '0;
      dscratch1_q <= '0;
      mscratch_q <= '0;
      mie_q <= '0;
      mtvec_q <= '0;
      mtvec_mode_q <= MTVEC_MODE;
    end else begin
      // update CSRs
      if (FPU == 1) begin
        frm_q    <= frm_n;
        fflags_q <= fflags_n;
        if (ZFINX == 0) begin
          mstatus_fs_q <= mstatus_fs_n;
        end
      end
      if (PULP_SECURE == 1) begin
        mstatus_q <= mstatus_n;
      end else begin
        mstatus_q <= '{
            uie: 1'b0,
            mie: mstatus_n.mie,
            upie: 1'b0,
            mpie: mstatus_n.mpie,
            mpp: PRIV_LVL_M,
            mprv: 1'b0
        };
      end
      mepc_q       <= mepc_n;
      mcause_q     <= mcause_n;
      depc_q       <= depc_n;
      dcsr_q       <= dcsr_n;
      dscratch0_q  <= dscratch0_n;
      dscratch1_q  <= dscratch1_n;
      mscratch_q   <= mscratch_n;
      mie_q        <= mie_n;
      mtvec_q      <= mtvec_n;
      mtvec_mode_q <= mtvec_mode_n;
    end
  end
  ////////////////////////////////////////////////////////////////////////
  //  ____       _                   _____     _                        //
  // |  _ \  ___| |__  _   _  __ _  |_   _| __(_) __ _  __ _  ___ _ __  //
  // | | | |/ _ \ '_ \| | | |/ _` |   | || '__| |/ _` |/ _` |/ _ \ '__| //
  // | |_| |  __/ |_) | |_| | (_| |   | || |  | | (_| | (_| |  __/ |    //
  // |____/ \___|_.__/ \__,_|\__, |   |_||_|  |_|\__, |\__, |\___|_|    //
  //                         |___/               |___/ |___/            //
  ////////////////////////////////////////////////////////////////////////

  if (DEBUG_TRIGGER_EN) begin : gen_trigger_regs
    // Register values
    logic        tmatch_control_exec_q;
    logic [31:0] tmatch_value_q;
    // Write enables
    logic        tmatch_control_we;
    logic        tmatch_value_we;

    // Write select
    assign tmatch_control_we = csr_we_int & debug_mode_i & (csr_addr_i == CSR_TDATA1);
    assign tmatch_value_we   = csr_we_int & debug_mode_i & (csr_addr_i == CSR_TDATA2);


    // Registers
    always_ff @(posedge clk or negedge rst_n) begin
      if (!rst_n) begin
        tmatch_control_exec_q <= 'b0;
        tmatch_value_q        <= 'b0;
      end else begin
        if (tmatch_control_we) tmatch_control_exec_q <= csr_wdata_int[2];
        if (tmatch_value_we) tmatch_value_q <= csr_wdata_int[31:0];
      end
    end

    // All supported trigger types
    assign tinfo_types = 1 << TTYPE_MCONTROL;

    // Assign read data
    // TDATA0 - only support simple address matching
    assign tmatch_control_rdata = {
      TTYPE_MCONTROL,  // type    : address/data match
      1'b1,  // dmode   : access from D mode only
      6'h00,  // maskmax : exact match only
      1'b0,  // hit     : not supported
      1'b0,  // select  : address match only
      1'b0,  // timing  : match before execution
      2'b00,  // sizelo  : match any access
      4'h1,  // action  : enter debug mode
      1'b0,  // chain   : not supported
      4'h0,  // match   : simple match
      1'b1,  // m       : match in m-mode
      1'b0,  // 0       : zero
      1'b0,  // s       : not supported
      PULP_SECURE == 1,  // u       : match in u-mode
      tmatch_control_exec_q,  // execute : match instruction address
      1'b0,  // store   : not supported
      1'b0
    };  // load    : not supported

    // TDATA1 - address match value only
    assign tmatch_value_rdata = tmatch_value_q;

    // Breakpoint matching
    // We match against the next address, as the breakpoint must be taken before execution
    assign trigger_match_o = tmatch_control_exec_q & (pc_id_i[31:0] == tmatch_value_q[31:0]);

  end else begin : gen_no_trigger_regs
    assign tinfo_types          = 'b0;
    assign tmatch_control_rdata = 'b0;
    assign tmatch_value_rdata   = 'b0;
    assign trigger_match_o      = 'b0;
  end

  /////////////////////////////////////////////////////////////////
  //   ____            __     ____                  _            //
  // |  _ \ ___ _ __ / _|   / ___|___  _   _ _ __ | |_ ___ _ __  //
  // | |_) / _ \ '__| |_   | |   / _ \| | | | '_ \| __/ _ \ '__| //
  // |  __/  __/ |  |  _|  | |__| (_) | |_| | | | | ||  __/ |    //
  // |_|   \___|_|  |_|(_)  \____\___/ \__,_|_| |_|\__\___|_|    //
  //                                                             //
  /////////////////////////////////////////////////////////////////

  // ------------------------
  // Events to count
  assign hpm_events[0] = 1'b1;  // cycle counter
  assign hpm_events[1] = mhpmevent_minstret_i;  // instruction counter
  assign hpm_events[2] = mhpmevent_ld_stall_i;  // nr of load use hazards
  assign hpm_events[3] = mhpmevent_jr_stall_i;  // nr of jump register hazards
  assign hpm_events[4]  = mhpmevent_imiss_i;                             // cycles waiting for instruction fetches, excluding jumps and branches
  assign hpm_events[5] = mhpmevent_load_i;  // nr of loads
  assign hpm_events[6] = mhpmevent_store_i;  // nr of stores
  assign hpm_events[7] = mhpmevent_jump_i;  // nr of jumps (unconditional)
  assign hpm_events[8] = mhpmevent_branch_i;  // nr of branches (conditional)
  assign hpm_events[9] = mhpmevent_branch_taken_i;  // nr of taken branches (conditional)
  assign hpm_events[10] = mhpmevent_compressed_i;  // compressed instruction counter
  assign hpm_events[11] = COREV_CLUSTER ? mhpmevent_pipe_stall_i : 1'b0;  // extra cycles from ELW
  assign hpm_events[12] = !APU ? 1'b0 : apu_typeconflict_i && !apu_dep_i;
  assign hpm_events[13] = !APU ? 1'b0 : apu_contention_i;
  assign hpm_events[14] = !APU ? 1'b0 : apu_dep_i && !apu_contention_i;
  assign hpm_events[15] = !APU ? 1'b0 : apu_wb_i;

  ///////////////////////////////////////////////////////////////////
  // PERFORMANCE COUNTER WRITE ENABLE DECODING
  ///////////////////////////////////////////////////////////////////
  logic mcounteren_we;      // Write enable for mcounteren (U-mode counter access)
  logic mcountinhibit_we;   // Write enable for mcountinhibit (counter disable)
  logic mhpmevent_we;       // Write enable for any mhpmevent[3:31]

  // Decode write enables for performance counter control CSRs
  assign mcounteren_we = csr_we_int & (csr_addr_i == CSR_MCOUNTEREN);
  assign mcountinhibit_we = csr_we_int & (csr_addr_i == CSR_MCOUNTINHIBIT);
  
  // Decode mhpmevent write: true for any of the 29 event selector CSRs
  assign mhpmevent_we     = csr_we_int & ( (csr_addr_i == CSR_MHPMEVENT3  )||
                                           (csr_addr_i == CSR_MHPMEVENT4  ) ||
                                           (csr_addr_i == CSR_MHPMEVENT5  ) ||
                                           (csr_addr_i == CSR_MHPMEVENT6  ) ||
                                           (csr_addr_i == CSR_MHPMEVENT7  ) ||
                                           (csr_addr_i == CSR_MHPMEVENT8  ) ||
                                           (csr_addr_i == CSR_MHPMEVENT9  ) ||
                                           (csr_addr_i == CSR_MHPMEVENT10 ) ||
                                           (csr_addr_i == CSR_MHPMEVENT11 ) ||
                                           (csr_addr_i == CSR_MHPMEVENT12 ) ||
                                           (csr_addr_i == CSR_MHPMEVENT13 ) ||
                                           (csr_addr_i == CSR_MHPMEVENT14 ) ||
                                           (csr_addr_i == CSR_MHPMEVENT15 ) ||
                                           (csr_addr_i == CSR_MHPMEVENT16 ) ||
                                           (csr_addr_i == CSR_MHPMEVENT17 ) ||
                                           (csr_addr_i == CSR_MHPMEVENT18 ) ||
                                           (csr_addr_i == CSR_MHPMEVENT19 ) ||
                                           (csr_addr_i == CSR_MHPMEVENT20 ) ||
                                           (csr_addr_i == CSR_MHPMEVENT21 ) ||
                                           (csr_addr_i == CSR_MHPMEVENT22 ) ||
                                           (csr_addr_i == CSR_MHPMEVENT23 ) ||
                                           (csr_addr_i == CSR_MHPMEVENT24 ) ||
                                           (csr_addr_i == CSR_MHPMEVENT25 ) ||
                                           (csr_addr_i == CSR_MHPMEVENT26 ) ||
                                           (csr_addr_i == CSR_MHPMEVENT27 ) ||
                                           (csr_addr_i == CSR_MHPMEVENT28 ) ||
                                           (csr_addr_i == CSR_MHPMEVENT29 ) ||
                                           (csr_addr_i == CSR_MHPMEVENT30 ) ||
                                           (csr_addr_i == CSR_MHPMEVENT31 ) );

  ///////////////////////////////////////////////////////////////////
  // PERFORMANCE COUNTER INCREMENT CALCULATION
  ///////////////////////////////////////////////////////////////////
  // Pre-compute incremented values for all 32 counters
  genvar incr_gidx;
  generate
    for (incr_gidx = 0; incr_gidx < 32; incr_gidx++) begin : gen_mhpmcounter_increment
      assign mhpmcounter_increment[incr_gidx] = mhpmcounter_q[incr_gidx] + 1;
    end
  endgenerate

  ///////////////////////////////////////////////////////////////////
  // PERFORMANCE COUNTER CONTROL CSR UPDATE LOGIC
  ///////////////////////////////////////////////////////////////////
  always_comb begin
    // Default: hold current values
    mcounteren_n    = mcounteren_q;
    mcountinhibit_n = mcountinhibit_q;
    mhpmevent_n     = mhpmevent_q;

    // mcounteren: U-mode counter access enable (PULP_SECURE=1 only)
    if (PULP_SECURE && mcounteren_we) mcounteren_n = csr_wdata_int;

    // mcountinhibit: Counter inhibit (disable counting)
    if (mcountinhibit_we) mcountinhibit_n = csr_wdata_int;

    // mhpmevent: Event selector for counters [3:31]
    if (mhpmevent_we) mhpmevent_n[csr_addr_i[4:0]] = csr_wdata_int;
  end

  ///////////////////////////////////////////////////////////////////
  // PERFORMANCE COUNTER WRITE/INCREMENT CONTROL
  ///////////////////////////////////////////////////////////////////
  genvar wcnt_gidx;
  generate
    for (wcnt_gidx = 0; wcnt_gidx < 32; wcnt_gidx++) begin : gen_mhpmcounter_write

      // Detect explicit writes to lower 32 bits (CSR_MCYCLE + offset)
      assign mhpmcounter_write_lower[wcnt_gidx] = csr_we_int && (csr_addr_i == (CSR_MCYCLE + wcnt_gidx));

      // Detect explicit writes to upper 32 bits (CSR_MCYCLEH + offset)
      assign mhpmcounter_write_upper[wcnt_gidx] = !mhpmcounter_write_lower[wcnt_gidx] &&
                                                  csr_we_int && (csr_addr_i == (CSR_MCYCLEH + wcnt_gidx)) && (MHPMCOUNTER_WIDTH == 64);

      // Determine when to auto-increment each counter
      if (!PULP_PERF_COUNTERS) begin : gen_no_pulp_perf_counters
        // STANDARD RISC-V MODE: Each counter tracks specific events
        
        if (wcnt_gidx == 0) begin : gen_mhpmcounter_mcycle
          // mcycle = mhpmcounter[0] : Increments every cycle (if not inhibited)
          assign mhpmcounter_write_increment[wcnt_gidx] = !mhpmcounter_write_lower[wcnt_gidx] &&
                                                          !mhpmcounter_write_upper[wcnt_gidx] &&
                                                          !mcountinhibit_q[wcnt_gidx];
        end else if (wcnt_gidx == 2) begin : gen_mhpmcounter_minstret
          // minstret = mhpmcounter[2] : Increments on retired instruction (if not inhibited)
          assign mhpmcounter_write_increment[wcnt_gidx] = !mhpmcounter_write_lower[wcnt_gidx] &&
                                                          !mhpmcounter_write_upper[wcnt_gidx] &&
                                                          !mcountinhibit_q[wcnt_gidx] &&
                                                          hpm_events[1];  // minstret event
        end else if( (wcnt_gidx>2) && (wcnt_gidx<(NUM_MHPMCOUNTERS+3))) begin : gen_mhpmcounter
          // mhpmcounter[3:31]: Increment if any selected event is active
          // Event selection controlled by mhpmevent[wcnt_gidx]
          assign mhpmcounter_write_increment[wcnt_gidx] = !mhpmcounter_write_lower[wcnt_gidx] &&
                                                          !mhpmcounter_write_upper[wcnt_gidx] &&
                                                          !mcountinhibit_q[wcnt_gidx] &&
                                                          |(hpm_events & mhpmevent_q[wcnt_gidx][NUM_HPM_EVENTS-1:0]);
        end else begin : gen_mhpmcounter_not_implemented
          // Counter not implemented
          assign mhpmcounter_write_increment[wcnt_gidx] = 1'b0;
        end
      end else begin : gen_pulp_perf_counters
        // PULP MODE: All counters share the same event register (non-standard)
        assign mhpmcounter_write_increment[wcnt_gidx] = !mhpmcounter_write_lower[wcnt_gidx] &&
                                                        !mhpmcounter_write_upper[wcnt_gidx] &&
                                                        !mcountinhibit_q[wcnt_gidx] &&
                                                        |(hpm_events & mhpmevent_q[wcnt_gidx][NUM_HPM_EVENTS-1:0]);
      end
    end
  endgenerate

  ///////////////////////////////////////////////////////////////////
  // PERFORMANCE COUNTER REGISTERS (mhpmcounter_q[0:31])
  ///////////////////////////////////////////////////////////////////
  // Counter layout:
  //   [0]  = mcycle (cycle counter)
  //   [1]  = Not implemented (reserved)
  //   [2]  = minstret (instruction counter)
  //   [3:NUM_MHPMCOUNTERS+2] = Programmable HPM counters
  //   [NUM_MHPMCOUNTERS+3:31] = Not implemented
  
  genvar cnt_gidx;
  generate
    for (cnt_gidx = 0; cnt_gidx < 32; cnt_gidx++) begin : gen_mhpmcounter
      if ((cnt_gidx == 1) || (cnt_gidx >= (NUM_MHPMCOUNTERS + 3))) begin : gen_non_implemented
        // Counter not implemented: tie to zero
        assign mhpmcounter_q[cnt_gidx] = 'b0;
      end else begin : gen_implemented
        always_ff @(posedge clk, negedge rst_n)
          if (!rst_n) begin
            mhpmcounter_q[cnt_gidx] <= 'b0;
          end else begin
            if (PULP_PERF_COUNTERS && (cnt_gidx == 2 || cnt_gidx == 0)) begin
              // PULP mode: mcycle and minstret not used
              mhpmcounter_q[cnt_gidx] <= 'b0;
            end else begin
              if (mhpmcounter_write_lower[cnt_gidx]) begin
                // Explicit write to lower 32 bits
                mhpmcounter_q[cnt_gidx][31:0] <= csr_wdata_int;
              end else if (mhpmcounter_write_upper[cnt_gidx]) begin
                // Explicit write to upper 32 bits (64-bit counters only)
                mhpmcounter_q[cnt_gidx][63:32] <= csr_wdata_int;
              end else if (mhpmcounter_write_increment[cnt_gidx]) begin
                // Auto-increment counter
                mhpmcounter_q[cnt_gidx] <= mhpmcounter_increment[cnt_gidx];
              end
            end
          end
      end
    end
  endgenerate

  ///////////////////////////////////////////////////////////////////
  // PERFORMANCE EVENT SELECTOR REGISTERS (mhpmevent_q[0:31])
  ///////////////////////////////////////////////////////////////////
  // Event selectors control which events increment each counter
  // Only counters [3:NUM_MHPMCOUNTERS+2] have event selectors
  
  genvar evt_gidx;
  generate
    for (evt_gidx = 0; evt_gidx < 32; evt_gidx++) begin : gen_mhpmevent
      if ((evt_gidx < 3) || (evt_gidx >= (NUM_MHPMCOUNTERS + 3))) begin : gen_non_implemented
        // Event selector not implemented: tie to zero
        assign mhpmevent_q[evt_gidx] = 'b0;
      end else begin : gen_implemented
        if (NUM_HPM_EVENTS < 32) begin : gen_tie_off
          // Tie off unused upper bits if fewer than 32 events
          assign mhpmevent_q[evt_gidx][31:NUM_HPM_EVENTS] = 'b0;
        end
        always_ff @(posedge clk, negedge rst_n)
          if (!rst_n) mhpmevent_q[evt_gidx][NUM_HPM_EVENTS-1:0] <= 'b0;
          else
            mhpmevent_q[evt_gidx][NUM_HPM_EVENTS-1:0] <= mhpmevent_n[evt_gidx][NUM_HPM_EVENTS-1:0];
      end
    end
  endgenerate

  ///////////////////////////////////////////////////////////////////
  // COUNTER ENABLE REGISTER (mcounteren_q[0:31])
  ///////////////////////////////////////////////////////////////////
  // Controls U-mode access to performance counters (PULP_SECURE=1 only)
  // Bit set: U-mode can read corresponding counter
  // Bit clear: U-mode access causes illegal instruction exception
  
  genvar en_gidx;
  generate
    for (en_gidx = 0; en_gidx < 32; en_gidx++) begin : gen_mcounteren
      if( (PULP_SECURE == 0) ||                     // Not used in M-mode only
          (en_gidx == 1) ||                          // Counter [1] not implemented
          (en_gidx >= (NUM_MHPMCOUNTERS+3) ) )       // Beyond implemented counters
        begin : gen_non_implemented
        assign mcounteren_q[en_gidx] = 'b0;
      end else begin : gen_implemented
        always_ff @(posedge clk, negedge rst_n)
          if (!rst_n) mcounteren_q[en_gidx] <= 'b0;  // Default: U-mode access disabled
          else mcounteren_q[en_gidx] <= mcounteren_n[en_gidx];
      end
    end
  endgenerate

  ///////////////////////////////////////////////////////////////////
  // COUNTER INHIBIT REGISTER (mcountinhibit_q[0:31])
  ///////////////////////////////////////////////////////////////////
  // Controls whether counters increment
  // Bit set: Counter disabled (does not increment)
  // Bit clear: Counter enabled (increments on events)
  // Note: Counters disabled out of reset to save power
  
  genvar inh_gidx;
  generate
    for (inh_gidx = 0; inh_gidx < 32; inh_gidx++) begin : gen_mcountinhibit
      if ((inh_gidx == 1) || (inh_gidx >= (NUM_MHPMCOUNTERS + 3))) begin : gen_non_implemented
        // Counter not implemented
        assign mcountinhibit_q[inh_gidx] = 'b0;
      end else begin : gen_implemented
        always_ff @(posedge clk, negedge rst_n)
          if (!rst_n) mcountinhibit_q[inh_gidx] <= 'b1;  // Default: counters inhibited (disabled)
          else mcountinhibit_q[inh_gidx] <= mcountinhibit_n[inh_gidx];
      end
    end
  endgenerate

`ifdef CV32E40P_ASSERT_ON

  ///////////////////////////////////////////////////////////////////
  // ASSERTIONS
  ///////////////////////////////////////////////////////////////////

  // Verify that mie_bypass_o correctly reflects the next-state mie value
  // This ensures the bypass mechanism works for back-to-back CSR instructions
  a_mie_bypass :
  assert property (@(posedge clk) disable iff (!rst_n) (1'b1) |-> (mie_bypass_o == mie_n));

`endif

endmodule
