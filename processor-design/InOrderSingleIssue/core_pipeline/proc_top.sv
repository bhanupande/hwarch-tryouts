// ===============================================================================
//  Module:      proc_top
//  Description: Top-level module for an in-order, single-issue RISC-V processor.
//               Connects all pipeline stages and manages instruction/data flow,
//               forwarding, and stalling for hazards.
//  Author:      Bhanu Pande
//  Date:        May 12, 2025
//  Revision:    1.0
// ===============================================================================

import rv32_pkg::*; // Import the package containing the instruction packet structure

module proc_top (
    input logic clk,       // Clock signal
    input logic resetn     // Active low reset signal
);

    // ==============================================================================
    // Signal Declarations
    // ==============================================================================
    // Inter-stage pipeline packets and control signals
    rv32_if_packet_t if_packet_out;             // IF -> OF: Instruction fetch output
    rv32_if_packet_t of_packet_in;              // IF -> OF: Operand fetch input
    rv32_instr_packet_t of_packet_out;          // OF -> EX: Decoded instruction packet
    rv32_issue_packet_t regfile_in_packet_out;  // OF -> EX: Issue packet from regfile
    rv32_issue_packet_t ex_packet_in;           // OF -> EX: Input to execute stage
    rv32_branch_packet_t ex2if_branch_packet;   // EX -> IF: Branch redirect info
    rv32_mem_packet_t exout_mem_packet;         // EX -> MEM: Memory access packet
    rv32_mem_packet_t ex2mem_mem_packet;        // EX -> MEM: Memory packet pipeline
    rv32_ex2mem_wb_packet_t exout_wb_packet;    // EX -> MEM: Write-back packet
    rv32_ex2mem_wb_packet_t ex2mem_wb_packet;   // EX -> MEM: Write-back packet pipeline
    rv32_ex_control_packet_t exout_control_packet; // EX -> MEM: Control signals
    rv32_ex_control_packet_t ex2mem_control_packet; // EX -> MEM: Control signals pipeline
    rv32_mem2wb_packet_t mem2wb_packet;         // MEM -> WB: Write-back packet
    rv32_mem2wb_packet_t wb_out_packet;         // MEM -> WB: Write-back packet pipeline
    rv32_fwd_packet_t fwd_packet;               // Forwarding info for data hazards

    logic instruction_commit; // Indicates instruction commit status
    logic stall_if;           // Stall signal for IF stage
    logic stall_ifof;         // Stall signal for IF -> OF pipeline
    logic stall_ofex;         // Stall signal for OF -> EX pipeline (unused here)
    logic stall_exmem;        // Stall signal for EX -> MEM pipeline (unused here)
    logic stall_memwb;        // Stall signal for MEM -> WB pipeline (unused here)
    logic dmem_ready;        // Memory ready signal from MEM stage

    // ==============================================================================
    // Dependency Control Module
    // ==============================================================================
    // Handles data hazard detection, forwarding, and pipeline stall control
    dependency_ctrl dep_ctrl_inst (
        .clk(clk),
        .resetn(resetn),
        .dmem_ready(dmem_ready),              // Data Memory ready signal
        .imem_ready(if_packet_out.mem_ready), // Instruction Memory ready signal
        .ofout_packet(of_packet_out),         // From OF stage
        .exout_wb_packet(exout_wb_packet),    // From EX stage
        .exout_mem_packet(exout_mem_packet),  // From EX stage (for loads/stores)
        .memout_packet(mem2wb_packet),        // From MEM stage
        .wbout_packet(wb_out_packet),         // From WB stage
        .fwd_packet(fwd_packet),              // Forwarding signals
        .stall_if(stall_if),                  // IF stage stall
        .stall_ifof(stall_ifof),              // IF/OF pipeline stall
        .stall_ofex(stall_ofex),              // OF/EX pipeline stall
        .stall_exmem(stall_exmem),            // EX/MEM pipeline stall
        .stall_memwb(stall_memwb)             // MEM/WB pipeline stall
    );

    // ==============================================================================
    // Instruction Fetch Stage
    // ==============================================================================
    // Fetches instructions from memory, handles branch redirection and stalls
    if_stage if_stage_inst (
        .clk(clk),
        .resetn(resetn),
        .branch_packet(ex2if_branch_packet),  // Branch redirect info from EX
        .stall_fetch(stall_if),               // Stall signal from dependency control
        .if_packet_out(if_packet_out)         // Output to IF/OF pipeline
    );

    // ==============================================================================
    // IF -> OF Pipeline Register
    // ==============================================================================
    // Transfers instruction packets from IF to OF stage, supports stalling
    pipe #(
        .PTYPE(rv32_if_packet_t)
    ) ifof_pipe (
        .din_packet(if_packet_out),
        .clk(clk),
        .resetn(resetn),
        .flush(ex2if_branch_packet.branch_taken), // Flush on branch taken
        .stall(stall_ifof),                   // Stall from dependency control
        .dout_packet(of_packet_in)
    );

    // ==============================================================================
    // Operand Fetch Stage
    // ==============================================================================
    // Decodes instructions, reads register operands, prepares for execution
    of_stage of_stage_inst (
        .if_packet(of_packet_in),             // Input from IF/OF pipeline
        .instruction_packet(of_packet_out)    // Output to regfile and EX stage
    );

    // ==============================================================================
    // OF -> EX Pipeline Register
    // ==============================================================================
    // Transfers issue packet from regfile to EX stage (no stall in this design)
    pipe #(
        .PTYPE(rv32_issue_packet_t)
    ) ofex_pipe (
        .din_packet(regfile_in_packet_out),
        .clk(clk),
        .resetn(resetn),
        .flush(ex2if_branch_packet.branch_taken), // Flush on branch taken
        .stall(stall_ofex),                         // No stall for OF -> EX
        .dout_packet(ex_packet_in)
    );

    // ==============================================================================
    // Execute Stage
    // ==============================================================================
    // Executes ALU operations, computes branches, prepares memory access/write-back
    execute_stage ex_stage_inst (
        .issued_instruction_packet(ex_packet_in), // Input from OF -> EX pipeline
        .fwd_packet(fwd_packet),                  // Forwarding info for hazards
        .branch_packet(ex2if_branch_packet),      // Output branch info to IF
        .mem_packet(exout_mem_packet),            // Output memory access packet
        .wb_packet(exout_wb_packet),              // Output write-back packet
        .ex_control_packet(exout_control_packet)  // Output control signals
    );

    // ==============================================================================
    // EX -> MEM Pipeline Registers
    // ==============================================================================
    // Transfers results and control signals from EX to MEM stage
    pipe #(
        .PTYPE(rv32_ex2mem_wb_packet_t)
    ) exmem_wb_pipe (
        .din_packet(exout_wb_packet),
        .clk(clk),
        .resetn(resetn),
        .flush(1'b0), // Flush on branch taken
        .stall(stall_exmem),                         // No stall for EX -> MEM
        .dout_packet(ex2mem_wb_packet)
    );

    pipe #(
        .PTYPE(rv32_mem_packet_t)
    ) exmem_mem_pipe (
        .din_packet(exout_mem_packet),
        .clk(clk),
        .resetn(resetn),
        .flush(1'b0), // Flush on branch taken
        .stall(stall_exmem),
        .dout_packet(ex2mem_mem_packet)
    );

    pipe #(
        .PTYPE(rv32_ex_control_packet_t)
    ) exmem_ctrl_pipe (
        .din_packet(exout_control_packet),
        .clk(clk),
        .resetn(resetn),
        .flush(1'b0), // Flush on branch taken
        .stall(stall_exmem),
        .dout_packet(ex2mem_control_packet)
    );

    // ==============================================================================
    // Memory Stage
    // ==============================================================================
    // Handles memory read/write operations, prepares data for write-back
    mem_stage mem_stage_inst (
        .clk(clk),
        .resetn(resetn),
        .wb_in_packet(ex2mem_wb_packet),         // Write-back info from EX
        .control_packet(ex2mem_control_packet),  // Control signals from EX
        .mem_packet(ex2mem_mem_packet),          // Memory access info from EX
        .dmem_ready(dmem_ready),                // Memory ready signal
        .wb_out_packet(mem2wb_packet)            // Output to MEM -> WB pipeline
    );

    // ==============================================================================
    // MEM -> WB Pipeline Register
    // ==============================================================================
    // Transfers write-back data from MEM to WB stage
    pipe #(
        .PTYPE(rv32_mem2wb_packet_t)
    ) mem_wb_pipe (
        .din_packet(mem2wb_packet),
        .clk(clk),
        .resetn(resetn),
        .stall(stall_memwb), // No stall for MEM -> WB
        .dout_packet(wb_out_packet)
    );

    // ==============================================================================
    // Register File Stage
    // ==============================================================================
    // Handles register file write-back and issues packets to EX stage
    regfile_stage regfile_inst (
        .clk(clk),
        .resetn(resetn),
        .instruction_packet(of_packet_out),      // Input from OF stage
        .writeback_packet(wb_out_packet),        // Input from MEM -> WB pipeline
        .issue_packet(regfile_in_packet_out),    // Output to OF -> EX pipeline
        .instruction_commit(instruction_commit)  // Commit status output
    );

endmodule