// Copyright 2020 Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License").
//
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
//
// You may obtain a copy of the License at:
//
//     https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS
// OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
//
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Arjan Bink - arjan.bink@silabs.com                         //
//                                                                            //
// Design Name:    Sleep Unit                                                 //
// Project Name:   CV32E40P                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Sleep unit containing the instantiated clock gate which    //
//                 provides the gated clock (clk_gated_o) for the rest        //
//                 of the design.                                             //
//                                                                            //
//                 The clock is gated for the following scenarios:            //
//                                                                            //
//                 - While waiting for fetch to become enabled                //
//                 - While blocked on a WFI (COREV_CLUSTER = 0)               //
//                 - While clock_en_i = 0 during a cv.elw (COREV_CLUSTER = 1) //
//                                                                            //
//                 Sleep is signaled via core_sleep_o when:                   //
//                                                                            //
//                 - During a cv.elw (except in debug (i.e. pending debug     //
//                   request, debug mode, single stepping, trigger match)     //
//                 - During a WFI (except in debug)                           //
//                                                                            //
// Requirements:   If COREV_CLUSTER = 1 the environment must guarantee:       //
//                                                                            //
//                 - If core_sleep_o    == 1'b0, then pulp_clock_en_i == 1'b1 //
//                 - If pulp_clock_en_i == 1'b0, then irq_i == 'b0            //
//                 - If pulp_clock_en_i == 1'b0, then debug_req_i == 1'b0     //
//                 - If pulp_clock_en_i == 1'b0, then instr_rvalid_i == 1'b0  //
//                 - If pulp_clock_en_i == 1'b0, then instr_gnt_i == 1'b0     //
//                 - If pulp_clock_en_i == 1'b0, then data_rvalid_i == 1'b0   //
//                 - If pulp_clock_en_i == 1'b0, then data_gnt_i == 1'b1      //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Module: cv32e40p_sleep_unit
///////////////////////////////////////////////////////////////////////////////
//
// FUNCTION:
//   Power management and clock gating control for CV32E40P core.
//   Provides main clock gate that stops core clock during sleep/idle periods.
//   Manages transitions between active, idle, and sleep states.
//
// POWER SAVING SCENARIOS:
//   1. Pre-fetch Enable:
//      - Clock gated until fetch_enable_i pulse received
//      - Prevents unnecessary toggling during reset/initialization
//      - Saves power when core held in reset state
//
//   2. WFI (Wait For Interrupt) - COREV_CLUSTER=0:
//      - RISC-V WFI instruction puts core to sleep
//      - Clock gated until interrupt or debug event
//      - Core state preserved, resumes on wake
//      - Typical use: idle loop in embedded systems
//
//   3. cv.elw (Event Load Word) - COREV_CLUSTER=1:
//      - PULP custom instruction for event-driven sleep
//      - Clock controlled by external pulp_clock_en_i
//      - Allows cluster-level power management
//      - Wakes on external event or data arrival
//
// TWO CONFIGURATION MODES:
//   COREV_CLUSTER=0 (Standalone Mode):
//     - Standard RISC-V behavior
//     - WFI instruction triggers sleep
//     - Core self-manages clock gating
//     - wake_from_sleep_i to exit sleep (interrupt, debug)
//
//   COREV_CLUSTER=1 (PULP Cluster Mode):
//     - Integrated with PULP cluster architecture
//     - cv.elw instruction enables cluster-controlled sleep
//     - External pulp_clock_en_i controls clock
//     - Cluster manages wake events centrally
//
// CLOCK GATING BENEFITS:
//   - Dynamic power reduction: P_dynamic = C × V² × f
//   - Stops clock tree toggling (largest dynamic power consumer)
//   - Typical savings: 60-90% of core dynamic power during sleep
//   - Leakage power unchanged (core still powered)
//
// STATE PRESERVATION:
//   During sleep:
//     ✓ All register contents preserved
//     ✓ PC and CSRs maintained
//     ✓ Pipeline state frozen
//     ✗ No instruction execution
//     ✗ No memory transactions
//     ✗ Clock tree stopped
//
// WAKE MECHANISMS:
//   Standalone (COREV_CLUSTER=0):
//     - Interrupt request (wake_from_sleep_i)
//     - Debug request
//     - NMI (Non-Maskable Interrupt)
//
//   PULP Cluster (COREV_CLUSTER=1):
//     - External cluster assertion of pulp_clock_en_i
//     - Event completion (p_elw_finish_i)
//     - Debug request
//
// DEBUG INTERACTION:
//   Sleep disabled during debug scenarios:
//     - Pending debug request
//     - Already in debug mode
//     - Single-step mode active
//     - Trigger match pending
//   This ensures debugger maintains core control
//
// TIMING CONSIDERATIONS:
//   Clock gate latency:
//     - Enable → Clock active: ~1-2 cycles
//     - Required for clock gate cell propagation
//     - Controller accounts for latency in FSM
//   
//   Wake latency:
//     - Depends on pipeline fill time
//     - Instruction buffer refill needed
//     - Typically 3-5 cycles from wake to execute
//
// VERIFICATION SUPPORT:
//   Extensive assertions for:
//     - Clock enable/disable conditions
//     - Sleep entry/exit protocol
//     - Debug mode interactions
//     - PULP cluster requirements
//
///////////////////////////////////////////////////////////////////////////////

module cv32e40p_sleep_unit #(
    // COREV_CLUSTER: Enables PULP cluster integration
    // 0: Standalone CV32E40P with WFI sleep
    // 1: PULP cluster mode with cv.elw and external clock control
    parameter COREV_CLUSTER = 0
) (
    ///////////////////////////////////////////////////////////////////////////
    // Clock and Reset Interface
    ///////////////////////////////////////////////////////////////////////////
    
    // Free-running clock - NEVER gated
    // Used to control clock gate itself and maintain sleep FSM state
    // Must always toggle even when core is sleeping
    input  logic clk_ungated_i,
    
    // Active-low asynchronous reset
    input  logic rst_n,
    
    // Gated clock output - feeds rest of CV32E40P core
    // This is the MAIN power-saving signal
    // Stops toggling during sleep/idle, reducing dynamic power
    output logic clk_gated_o,
    
    // Scan chain enable for DFT (Design For Test)
    // When high, disables all clock gating for manufacturing test
    // Allows scan chains to operate through clock gates
    input  logic scan_cg_en_i,

    ///////////////////////////////////////////////////////////////////////////
    // Core Sleep Status
    ///////////////////////////////////////////////////////////////////////////
    
    // Indicates core is in sleep mode
    // System can use this to:
    //   - Gate external clocks (COREV_CLUSTER=0)
    //   - Power down peripherals
    //   - Enter system-level sleep states
    // Asserted during: WFI sleep OR cv.elw sleep (depending on COREV_CLUSTER)
    output logic core_sleep_o,

    ///////////////////////////////////////////////////////////////////////////
    // Fetch Enable Control
    ///////////////////////////////////////////////////////////////////////////
    
    // Fetch enable input from system
    // Single pulse transitions core from reset to active
    // Once pulsed, fetch_enable_o stays high (sticky)
    input  logic fetch_enable_i,
    
    // Fetch enable output to controller
    // Sticky version of fetch_enable_i
    // Remains high after initial pulse
    output logic fetch_enable_o,

    ///////////////////////////////////////////////////////////////////////////
    // Core Busy Status Inputs
    ///////////////////////////////////////////////////////////////////////////
    // Indicate which pipeline stages/units have pending operations
    // Clock cannot be gated until all relevant units report not busy
    
    input logic if_busy_i,    // Instruction fetch stage busy (prefetching, waiting for grant)
    input logic ctrl_busy_i,  // Controller busy (FSM transitions, debug)
    input logic lsu_busy_i,   // Load/store unit busy (pending memory transaction)
    input logic apu_busy_i,   // Auxiliary Processing Unit busy (coprocessor operation)

    ///////////////////////////////////////////////////////////////////////////
    // PULP Cluster Interface (only used if COREV_CLUSTER=1)
    ///////////////////////////////////////////////////////////////////////////
    
    // External clock enable from PULP cluster
    // Cluster asserts to wake core, deasserts to sleep
    // Gives cluster-level power management control
    input logic pulp_clock_en_i,
    
    // cv.elw (Event Load Word) instruction tracking
    // p_elw_start_i: Asserted when cv.elw instruction starts (data_req_o)
    // p_elw_finish_i: Asserted when cv.elw completes (data_rvalid_i)
    // Between start and finish, core can sleep if pulp_clock_en_i=0
    input logic p_elw_start_i,
    input logic p_elw_finish_i,
    
    // Debug override for cv.elw sleep
    // When high, prevents sleep during cv.elw (debug mode active)
    input logic debug_p_elw_no_sleep_i,

    ///////////////////////////////////////////////////////////////////////////
    // WFI Wake Interface (only used if COREV_CLUSTER=0)
    ///////////////////////////////////////////////////////////////////////////
    
    // Wake from WFI sleep
    // Asserted by controller when:
    //   - Interrupt pending
    //   - Debug request
    //   - NMI
    // Causes clock_en to assert and core to resume
    input logic wake_from_sleep_i
);

  import cv32e40p_pkg::*;

  ///////////////////////////////////////////////////////////////////////////
  // INTERNAL SIGNALS
  ///////////////////////////////////////////////////////////////////////////
  
  // Sticky fetch enable (remains high after first pulse)
  logic fetch_enable_q;  // Registered version
  logic fetch_enable_d;  // Next state
  
  // Core busy tracking
  // Indicates core has unfinished business before can enter sleep
  logic              core_busy_q;               // Current busy state
  logic core_busy_d;  // Next busy state
  
  // cv.elw transaction tracking (PULP cluster only)
  logic p_elw_busy_q;  // Currently executing cv.elw?
  logic p_elw_busy_d;  // Next state
  
  // Final clock enable signal feeding clock gate
  // When 0: Clock gated (core asleep/idle)
  // When 1: Clock running (core active)
  logic clock_en;

  //////////////////////////////////////////////////////////////////////////////
  // SLEEP FINITE STATE MACHINE
  //////////////////////////////////////////////////////////////////////////////
  // Controls clock gating based on core busy status and configuration mode
  //
  // STATE MACHINE OVERVIEW:
  //   Tracks core busy/idle state to determine when safe to gate clock
  //   Two modes of operation based on COREV_CLUSTER parameter
  //
  // STICKY FETCH ENABLE:
  //   fetch_enable_i is typically a single-cycle pulse
  //   Core needs persistent enable, so make it sticky
  //   Once high, remains high forever (no way to go back to pre-enable state)
  //
  // BUSY SIGNAL AGGREGATION:
  //   Different criteria for each mode:
  //     PULP Cluster: Only care about IF/APU during cv.elw
  //     Standalone: Care about all units (IF/CTRL/LSU/APU)
  //
  // CLOCK ENABLE LOGIC:
  //   Clock enabled when:
  //     - fetch_enable_q is high (core initialized), AND
  //     - (core_busy_q OR wake condition)
  //   Wake condition:
  //     PULP: pulp_clock_en_i (external control)
  //     Standalone: wake_from_sleep_i (interrupt/debug)
  //
  //////////////////////////////////////////////////////////////////////////////

  // Make sticky version of fetch_enable_i
  // Once asserted, stays asserted
  // Allows single-pulse input to create persistent enable
  assign fetch_enable_d = fetch_enable_i ? 1'b1 : fetch_enable_q;

  generate
    if (COREV_CLUSTER) begin : g_pulp_sleep
      
      ///////////////////////////////////////////////////////////////////////////
      // PULP CLUSTER MODE (COREV_CLUSTER=1)
      ///////////////////////////////////////////////////////////////////////////
      // cv.elw instruction enables event-driven sleep
      // External cluster controls clock via pulp_clock_en_i
      //
      // BUSY LOGIC:
      //   During cv.elw: Only IF and APU matter
      //     - IF busy: Prefetch buffer filling
      //     - APU busy: Coprocessor operation ongoing
      //     - LSU/CTRL not checked (cv.elw handles its own LSU transaction)
      //   Outside cv.elw: Always busy (normal operation, no sleep)
      //
      // CLOCK ENABLE:
      //   fetch_enable_q AND (pulp_clock_en_i OR core_busy_q)
      //   Cluster can gate clock by deasserting pulp_clock_en_i
      //   Only possible when core_busy_q=0 (core ready to sleep)
      //
      // SLEEP INDICATION:
      //   core_sleep_o = cv.elw active AND not busy AND not debug
      //   System can use this for:
      //     - Power down peripherals
      //     - System-level sleep modes
      //     - Event routing configuration
      //
      // CV.ELW STATE MACHINE:
      //   p_elw_start_i:  Load instruction issues data request
      //   p_elw_busy: Active between start and finish
      //   p_elw_finish_i: Data response received, load completes
      //   During busy window: Clock can be gated if pulp_clock_en_i=0
      //

      // Busy unless in a cv.elw and IF/APU are no longer busy
      // Logic: If in cv.elw, check IF/APU. Otherwise, always busy.
      assign core_busy_d = p_elw_busy_d ? (if_busy_i || apu_busy_i) : 1'b1;

      // Enable the clock only after the initial fetch enable while busy or instructed so by PULP Cluster's pulp_clock_en_i
      // Cluster can remove clock when core not busy and doesn't need to be awake
      assign clock_en = fetch_enable_q && (pulp_clock_en_i || core_busy_q);

      // Sleep only in response to cv.elw once no longer busy (but not during various debug scenarios)
      // Debug scenarios: single-step, debug mode, pending debug req, trigger match
      assign core_sleep_o = p_elw_busy_d && !core_busy_q && !debug_p_elw_no_sleep_i;

      // cv.elw is busy between load start and load finish (data_req_o / data_rvalid_i)
      // Acts as SR latch: Set on start, reset on finish
      assign p_elw_busy_d = p_elw_start_i ? 1'b1 : (p_elw_finish_i ? 1'b0 : p_elw_busy_q);

    end else begin : g_no_pulp_sleep
      
      ///////////////////////////////////////////////////////////////////////////
      // STANDALONE MODE (COREV_CLUSTER=0)
      ///////////////////////////////////////////////////////////////////////////
      // Standard RISC-V WFI (Wait For Interrupt) sleep
      // Core self-manages clock gating
      //
      // BUSY LOGIC:
      //   Check all pipeline stages and units:
      //     - IF: Instruction fetch / prefetch buffer
      //     - CTRL: Controller FSM / debug
      //     - LSU: Load/store unit pending transactions
      //     - APU: Coprocessor operations
      //   Any unit busy → core busy, cannot sleep
      //
      // CLOCK ENABLE:
      //   fetch_enable_q AND (wake_from_sleep_i OR core_busy_q)
      //   Clock disabled only when:
      //     - Core not busy (safe to stop)
      //     - No wake event pending
      //     - fetch_enable received (initialized)
      //   This happens during WFI instruction execution
      //
      // SLEEP INDICATION:
      //   core_sleep_o = fetch_enable_q AND !clock_en
      //   Sleep only when:
      //     - Core initialized (fetch_enable_q)
      //     - Clock actually gated (!clock_en)
      //   Indicates to system: Safe to gate clk_ungated_i externally
      //
      // WAKE MECHANISM:
      //   wake_from_sleep_i asserted by controller when:
      //     - Interrupt pending (and interrupts enabled)
      //     - Debug request
      //     - NMI (Non-Maskable Interrupt)
      //   Immediately re-enables clock
      //

      // Busy when any of the sub units is busy (typically wait for the instruction buffer to fill up)
      // All units must be idle before can enter sleep
      assign core_busy_d = if_busy_i || ctrl_busy_i || lsu_busy_i || apu_busy_i;

      // Enable the clock only after the initial fetch enable while busy or waking up to become busy
      // wake_from_sleep_i: Interrupt or debug event requires core wake
      assign clock_en = fetch_enable_q && (wake_from_sleep_i || core_busy_q);

      // Sleep only in response to WFI which leads to clock disable; debug_wfi_no_sleep_o in
      // cv32e40p_controller determines the scenarios for which WFI can(not) cause sleep.
      // Sleep occurs when fetch enabled but clock disabled (WFI executed, no wake pending)
      assign core_sleep_o = fetch_enable_q && !clock_en;

      // cv.elw does not exist for COREV_CLUSTER = 0
      assign p_elw_busy_d = 1'b0;

    end
  endgenerate

  ///////////////////////////////////////////////////////////////////////////
  // STATE REGISTERS
  ///////////////////////////////////////////////////////////////////////////
  // Clocked by ungated clock (must run even when core sleeping)
  // Maintains sleep FSM state and control signals
  //
  always_ff @(posedge clk_ungated_i, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      core_busy_q    <= 1'b0;
      p_elw_busy_q   <= 1'b0;
      fetch_enable_q <= 1'b0;
    end else begin
      core_busy_q    <= core_busy_d;
      p_elw_busy_q   <= p_elw_busy_d;
      fetch_enable_q <= fetch_enable_d;
    end
  end

  ///////////////////////////////////////////////////////////////////////////
  // FETCH ENABLE OUTPUT
  ///////////////////////////////////////////////////////////////////////////
  // Provides sticky fetch enable to controller
  // Controller uses this to exit RESET state and begin fetching
  assign fetch_enable_o = fetch_enable_q;

  ///////////////////////////////////////////////////////////////////////////
  // MAIN CORE CLOCK GATE
  ///////////////////////////////////////////////////////////////////////////
  // Primary power-saving mechanism for CV32E40P
  //
  // CLOCK GATE OPERATION:
  //   Input: clk_ungated_i (free-running, always toggles)
  //   Enable: clock_en (computed by sleep FSM above)
  //   Output: clk_gated_o (feeds entire core pipeline)
  //
  // CLOCK GATE CELL:
  //   Typically an integrated clock gate (ICG) cell
  //   Latch-based to prevent glitches:
  //     - Enable sampled on clock LOW phase
  //     - Output updated on clock HIGH phase
  //   Glitch-free transitions critical for functional correctness
  //
  // POWER SAVINGS:
  //   When clock_en=0 (sleep):
  //     - Core clock tree stops toggling
  //     - Dynamic power: P = C×V²×f → f=0 → P≈0
  //     - Typical core dynamic power reduction: 70-95%
  //     - Leakage power unchanged (core still powered)
  //   
  //   Clock tree is major power consumer:
  //     - Drives all pipeline registers (~2000 FFs)
  //     - Large capacitive load
  //     - Frequent toggling (every cycle when active)
  //
  // TIMING:
  //   Enable → Output propagation: 1-2 ungated clock cycles
  //   This latency is why core_busy_q is registered
  //   Controller FSM accounts for clock gate latency
  //
  // SCAN MODE:
  //   scan_cg_en_i=1 bypasses clock gate
  //   Allows manufacturing test scan chains to operate
  //   All logic remains scannable despite clock gating
  //
  // Main clock gate of CV32E40P
  cv32e40p_clock_gate core_clock_gate_i (
      .clk_i       (clk_ungated_i),  // Free-running input clock
      .en_i        (clock_en),       // Enable from sleep FSM
      .scan_cg_en_i(scan_cg_en_i),   // Bypass for scan mode
      .clk_o       (clk_gated_o)     // Gated output to core
  );

  //////////////////////////////////////////////////////////////////////////////
  // FORMAL VERIFICATION ASSERTIONS
  //////////////////////////////////////////////////////////////////////////////
  // Comprehensive checks for clock gating safety and correctness
  //
  // ASSERTION CATEGORIES:
  //   1. Clock enable/disable conditions
  //   2. Sleep entry/exit protocol
  //   3. Interaction with controller FSM states
  //   4. Debug mode interactions
  //   5. PULP cluster requirements (COREV_CLUSTER=1)
  //   6. Standalone requirements (COREV_CLUSTER=0)
  //
  // WHY ASSERTIONS ARE CRITICAL:
  //   Clock gating bugs can cause:
  //     - Lost interrupts (clock gated when should be active)
  //     - Incorrect wake (clock enabled at wrong time)
  //     - Debug failures (can't wake core for debug)
  //     - Functional corruption (state lost during improper gate)
  //   Assertions catch these issues in simulation/formal verification
  //
  // HIERARCHICAL REFERENCES:
  //   Assertions access controller FSM: id_stage_i.controller_i.ctrl_fsm_cs
  //   Required because sleep unit needs to coordinate with controller states
  //   Ensures clock gating aligns with pipeline state machine
  //
  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------

`ifdef CV32E40P_ASSERT_ON

  ///////////////////////////////////////////////////////////////////////////
  // COMMON ASSERTIONS (both modes)
  ///////////////////////////////////////////////////////////////////////////

  // Clock gate is disabled during RESET state of the controller
  // RESET state: Core in reset, no operations should occur
  // Clock disabled to save power during extended reset
  property p_clock_en_0;
    @(posedge clk_ungated_i) disable iff (!rst_n) ((id_stage_i.controller_i.ctrl_fsm_cs == cv32e40p_pkg::RESET) && (id_stage_i.controller_i.ctrl_fsm_ns == cv32e40p_pkg::RESET)) |-> (clock_en == 1'b0);
  endproperty

  a_clock_en_0 :
  assert property (p_clock_en_0);

  // Clock gate is enabled when exit from RESET state is required
  // Transition out of RESET: Need clock to initialize pipeline
  // Must enable clock before first fetch can occur
  property p_clock_en_1;
    @(posedge clk_ungated_i) disable iff (!rst_n) ((id_stage_i.controller_i.ctrl_fsm_cs == cv32e40p_pkg::RESET) && (id_stage_i.controller_i.ctrl_fsm_ns != cv32e40p_pkg::RESET)) |-> (clock_en == 1'b1);
  endproperty

  a_clock_en_1 :
  assert property (p_clock_en_1);

  // Clock gate is not enabled before receiving fetch_enable_i pulse
  // Before fetch_enable: Core should remain idle
  // Prevents premature operation before system ready
  property p_clock_en_2;
    @(posedge clk_ungated_i) disable iff (!rst_n) (fetch_enable_q == 1'b0) |-> (clock_en == 1'b0);
  endproperty

  a_clock_en_2 :
  assert property (p_clock_en_2);

  generate
    if (COREV_CLUSTER) begin : g_pulp_cluster_assertions

      ///////////////////////////////////////////////////////////////////////////
      // PULP CLUSTER MODE ASSERTIONS (COREV_CLUSTER=1)
      ///////////////////////////////////////////////////////////////////////////
      
      // Clock gate is only possibly disabled in RESET or when COREV_CLUSTER disables clock
      // Valid disable conditions:
      //   1. RESET state: Initialization
      //   2. pulp_clock_en_i=0: Cluster-controlled sleep during cv.elw
      property p_clock_en_3;
        @(posedge clk_ungated_i) disable iff (!rst_n) (clock_en == 1'b0) -> ((id_stage_i.controller_i.ctrl_fsm_cs == cv32e40p_pkg::RESET) || (COREV_CLUSTER && !pulp_clock_en_i));
      endproperty

      a_clock_en_3 :
      assert property (p_clock_en_3);

      // Core can only sleep in response to cv.elw
      // PULP mode: Only cv.elw instruction causes sleep
      // WFI does NOT cause sleep in PULP mode (different use case)
      property p_only_sleep_during_p_elw;
        @(posedge clk_ungated_i) disable iff (!rst_n) (core_sleep_o == 1'b1) |-> (p_elw_busy_d == 1'b1);
      endproperty

      a_only_sleep_during_p_elw :
      assert property (p_only_sleep_during_p_elw);


      // Environment fully controls clock_en during sleep
      // When sleeping, cluster has full control via pulp_clock_en_i
      // Core doesn't override cluster's clock gating decision
      property p_full_clock_en_control;
        @(posedge clk_ungated_i) disable iff (!rst_n) (core_sleep_o == 1'b1) |-> (pulp_clock_en_i == clock_en);
      endproperty

      a_full_clock_en_control :
      assert property (p_full_clock_en_control);

    end else begin : g_no_pulp_cluster_assertions

      ///////////////////////////////////////////////////////////////////////////
      // STANDALONE MODE ASSERTIONS (COREV_CLUSTER=0)
      ///////////////////////////////////////////////////////////////////////////

      // Clock gate is only possibly disabled in RESET or SLEEP
      // Valid disable conditions:
      //   1. RESET state: Pre-initialization
      //   2. SLEEP state: WFI-induced sleep
      property p_clock_en_4;
        @(posedge clk_ungated_i) disable iff (!rst_n) (clock_en == 1'b0) -> ((id_stage_i.controller_i.ctrl_fsm_cs == cv32e40p_pkg::RESET) || (id_stage_i.controller_i.ctrl_fsm_ns == cv32e40p_pkg::SLEEP));
      endproperty

      a_clock_en_4 :
      assert property (p_clock_en_4);

      // Clock gate is enabled when exit from SLEEP state is required
      // Wake event: Interrupt, debug, NMI
      // Must enable clock to process wake event
      property p_clock_en_5;
        @(posedge clk_ungated_i) disable iff (!rst_n)  ((id_stage_i.controller_i.ctrl_fsm_cs == cv32e40p_pkg::SLEEP) && (id_stage_i.controller_i.ctrl_fsm_ns != cv32e40p_pkg::SLEEP)) |-> (clock_en == 1'b1);
      endproperty

      a_clock_en_5 :
      assert property (p_clock_en_5);

      // Core sleep is only signaled in SLEEP state
      // core_sleep_o should perfectly align with SLEEP FSM state
      // System relies on this for external power management
      property p_core_sleep;
        @(posedge clk_ungated_i) disable iff (!rst_n) (core_sleep_o == 1'b1) -> ((id_stage_i.controller_i.ctrl_fsm_cs == cv32e40p_pkg::SLEEP));
      endproperty

      a_core_sleep :
      assert property (p_core_sleep);

      // Core can only become non-busy due to SLEEP entry
      // Transition to not-busy only happens when entering/in sleep
      // Prevents spurious idle periods outside sleep protocol
      property p_non_busy;
        @(posedge clk_ungated_i) disable iff (!rst_n) (core_busy_d == 1'b0) |-> (id_stage_i.controller_i.ctrl_fsm_cs == cv32e40p_pkg::WAIT_SLEEP) || (id_stage_i.controller_i.ctrl_fsm_cs == cv32e40p_pkg::SLEEP);
      endproperty

      a_non_busy :
      assert property (p_non_busy);

      // During (COREV_CLUSTER = 0) sleep it should be allowed to externally gate clk_i
      // Sleep state must be stable: No internal state changes
      // System can safely gate clk_ungated_i externally
      // All state registers hold their values (no toggles needed)
      property p_gate_clk_i;
        @(posedge clk_ungated_i) disable iff (!rst_n) (core_sleep_o == 1'b1) |-> (core_busy_q == core_busy_d) && (p_elw_busy_q == p_elw_busy_d) && (fetch_enable_q == fetch_enable_d);
      endproperty

      a_gate_clk_i :
      assert property (p_gate_clk_i);

      // During sleep the internal clock is gated
      // core_sleep_o=1 implies clock_en=0
      // Ensures clock actually stopped when claiming sleep
      property p_gate_clock_during_sleep;
        @(posedge clk_ungated_i) disable iff (!rst_n) (core_sleep_o == 1'b1) |-> (clock_en == 1'b0);
      endproperty

      a_gate_clock_during_sleep :
      assert property (p_gate_clock_during_sleep);

      // Sleep mode can only be entered in response to a WFI instruction
      // Check instruction is WFI encoding: 0x10500073
      // OPCODE_SYSTEM = 7'b1110011
      // funct12 = 12'b000100000101 (WFI)
      // Ensures only WFI causes sleep, not other instructions
      property p_only_sleep_for_wfi;
        @(posedge clk_ungated_i) disable iff (!rst_n) (core_sleep_o == 1'b1) |-> (id_stage_i.instr == {
          12'b000100000101, 13'b0, OPCODE_SYSTEM
        });
      endproperty

      a_only_sleep_for_wfi :
      assert property (p_only_sleep_for_wfi);

      // In sleep mode the core will not be busy (e.g. no ongoing/outstanding instruction or data transactions)
      // Sleep only safe when all units idle
      // No pending memory transactions, no pipeline activity
      property p_not_busy_during_sleep;
        @(posedge clk_ungated_i) disable iff (!rst_n) (core_sleep_o == 1'b1) |-> ((core_busy_q == 1'b0) && (core_busy_d == 1'b0));
      endproperty

      a_not_busy_during_sleep :
      assert property (p_not_busy_during_sleep);

    end
  endgenerate

`endif

  ///////////////////////////////////////////////////////////////////////////
  // END OF MODULE
  ///////////////////////////////////////////////////////////////////////////
  //
  // SLEEP UNIT SUMMARY:
  //
  // KEY CAPABILITIES:
  //   - Main clock gating for dynamic power savings (60-95% reduction)
  //   - Two modes: WFI sleep (standalone) or cv.elw sleep (PULP cluster)
  //   - Safe sleep entry: All pipeline stages idle before gating
  //   - Fast wake: 3-5 cycle latency from interrupt to execution
  //   - Debug-aware: Sleep disabled during debug operations
  //
  // POWER SAVINGS BREAKDOWN:
  //   Dynamic power eliminated:
  //     - Clock tree distribution network (~40% of core dynamic power)
  //     - Pipeline register switching (~30%)
  //     - Control logic toggling (~30%)
  //   Power still consumed:
  //     - Leakage power (core remains powered)
  //     - Ungated clock tree (minimal load)
  //
  // INTEGRATION REQUIREMENTS:
  //   Standalone (COREV_CLUSTER=0):
  //     - Connect wake_from_sleep_i to interrupt/debug logic
  //     - Optional: Gate clk_ungated_i externally when core_sleep_o=1
  //
  //   PULP Cluster (COREV_CLUSTER=1):
  //     - Drive pulp_clock_en_i from cluster controller
  //     - Connect p_elw_start/finish_i to LSU
  //     - Ensure environment meets requirements in header
  //
  // ALTERNATIVE IMPLEMENTATIONS:
  //   1. Voltage scaling: Further power savings but complex
  //   2. Power gating: Zero leakage but lose state, slow wake
  //   3. Multi-level gating: Gate different domains separately
  //   4. Adaptive gating: Dynamic threshold based on workload
  //

endmodule  // cv32e40p_sleep_unit
