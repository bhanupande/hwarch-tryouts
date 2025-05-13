// ***********************************************************************
// Module: proc_top
// Description: Top-level module for an in-order single-issue processor.
//              This module connects various pipeline stages and handles
//              the flow of instruction packets through the pipeline.
// Author: Bhanu Pande
// Date: May 12, 2025
// ***********************************************************************

import rv32_pkg::*; // Import the package containing the instruction packet structure

module proc_top (
    input logic clk,       // Clock signal
    input logic resetn     // Active low reset signal
);

    // ***********************************************************************
    // Signal Declarations
    // ***********************************************************************
    // Declare signals for inter-stage communication and control
    rv32_if_packet_t if_packet_out;             // Output instruction packet from instruction fetch stage
    rv32_if_packet_t of_packet_in;              // Input instruction packet to the Operand Fetch stage
    rv32_instr_packet_t of_packet_out;          // Output instruction packet from Operand Fetch stage
    rv32_issue_packet_t regfile_in_packet_out;  // Output instruction packet from Operand Fetch stage
    rv32_issue_packet_t ex_packet_in;           // Input instruction packet to the Execute stage
    rv32_branch_packet_t ex2if_branch_packet;   // Branch packet output for instruction fetch redirection
    rv32_mem_packet_t exout_mem_packet;         // Memory access packet output from Execute stage
    rv32_mem_packet_t ex2mem_mem_packet;        // Memory access packet input to Memory stage
    rv32_ex2mem_wb_packet_t exout_wb_packet;    // Write-back packet output from Execute stage
    rv32_ex2mem_wb_packet_t ex2mem_wb_packet;   // Write-back packet input to Memory stage
    rv32_ex_control_packet_t exout_control_packet; // Control signals for memory operations from Execute stage
    rv32_ex_control_packet_t ex2mem_control_packet; // Control signals for memory operations to Memory stage
    rv32_mem2wb_packet_t mem2wb_packet;         // Write-back packet output from Memory stage
    rv32_mem2wb_packet_t wb_out_packet;         // Write-back packet input to Register File stage
    rv32_fwd_packet_t fwd_packet;               // Forwarding packet for data hazards

    logic instruction_commit; // Signal indicating instruction commit status
    logic stall_if;          // Stall signal for Instruction Fetch stage
    logic stall_ifof;        // Stall signal for IF -> OF pipeline
    logic stall_ofex;        // Stall signal for IF -> OF -> EX pipeline
    logic stall_exmem;       // Stall signal for IF -> OF -> EX -> MEM pipeline
    logic stall_memwb;       // Stall signal for MEM -> WB pipeline

    // ***********************************************************************
    // Dependency Control Module
    // ***********************************************************************
    // Handles pipeline stalls and dependencies between stages
    dependency_ctrl dep_ctrl_inst (
        .clk(clk),                          // Clock signal
        .resetn(resetn),                    // Active low reset signal
        .if_out_packet(if_packet_out),      // Instruction packet from IF stage
        .of_in_packet(of_packet_in),        // Instruction packet to OF stage
        .of_out_packet(of_packet_out),      // Instruction packet from OF stage
        .ex_in_packet(ex_packet_in),        // Instruction packet to EX stage
        .ex2mem_mem_packet(ex2mem_mem_packet), // Memory packet to MEM stage
        .exout_wb_packet(exout_wb_packet),  // Write-back packet from EX stage
        .ex2mem_wb_packet(ex2mem_wb_packet), // Write-back packet to MEM stage
        .ex2mem_control_packet(ex2mem_control_packet), // Control packet to MEM stage
        .mem2wb_packet(mem2wb_packet),      // Write-back packet from MEM stage
        .wb_out_packet(wb_out_packet),      // Write-back packet to WB stage
        .fwd_packet(fwd_packet),            // Forwarding packet for data hazards
        .stall_if(stall_if),                // Stall signal for IF stage
        .stall_ifof(stall_ifof),            // Stall signal for IF -> OF pipeline
        .stall_ofex(stall_ofex),            // Stall signal for IF -> OF -> EX pipeline
        .stall_exmem(stall_exmem),          // Stall signal for IF -> OF -> EX -> MEM pipeline
        .stall_memwb(stall_memwb)           // Stall signal for MEM -> WB pipeline
    );

    // ***********************************************************************
    // Instruction Fetch Stage
    // ***********************************************************************
    // Fetches instructions from memory and outputs them to the pipeline
    if_stage if_stage_inst (
        .clk(clk),                          // Clock signal
        .resetn(resetn),                    // Active low reset signal
        .branch_packet(ex2if_branch_packet), // Input branch packet for redirection
        .stall_fetch(stall_if),             // Stall signal for IF stage
        .if_packet_out(if_packet_out)       // Output instruction packet
    );

    // Pipeline: IF -> OF
    // Transfers instruction packets from the Instruction Fetch stage to the Operand Fetch stage
    pipe #(
        .PTYPE(rv32_if_packet_t) // Specify the type of the packet
    ) ifof_pipe (
        .din_packet(if_packet_out), // Input packet from IF stage
        .clk(clk),                  // Clock signal
        .resetn(resetn),            // Active low reset signal
        .stall(stall_ifof),         // Stall signal for IF -> OF pipeline
        .dout_packet(of_packet_in)  // Output packet to OF stage
    );

    // ***********************************************************************
    // Operand Fetch Stage
    // ***********************************************************************
    // Decodes instructions and prepares operands for execution
    of_stage of_stage_inst (
        .if_packet(of_packet_in),          // Input instruction packet from IF stage
        .instruction_packet(of_packet_out) // Output instruction packet to EX stage
    );

    // Pipeline: OF -> EX
    // Transfers instruction packets from the Operand Fetch stage to the Execute stage
    pipe #(
        .PTYPE(rv32_issue_packet_t) // Specify the type of the packet
    ) ofex_pipe (
        .din_packet(regfile_in_packet_out), // Input packet from Operand Fetch stage
        .clk(clk),                          // Clock signal
        .resetn(resetn),                    // Active low reset signal
        .stall(stall_ofex),                 // Stall signal for OF -> EX pipeline
        .dout_packet(ex_packet_in)          // Output packet to Execute stage
    );

    // ***********************************************************************
    // Execute Stage
    // ***********************************************************************
    // Executes instructions and generates results for memory or write-back
    execute_stage ex_stage_inst (
        .issued_instruction_packet(ex_packet_in), // Input instruction packet from OF stage
        .fwd_packet(fwd_packet),                  // Forwarding packet for data hazards
        .branch_packet(ex2if_branch_packet),      // Output branch packet for redirection
        .mem_packet(exout_mem_packet),            // Output memory access packet
        .wb_packet(exout_wb_packet),              // Output write-back packet
        .ex_control_packet(exout_control_packet)  // Output control packet
    );

    // Pipelines: EX -> MEM
    // Transfers results from the Execute stage to the Memory stage
    pipe #(
        .PTYPE(rv32_ex2mem_wb_packet_t) // Specify the type of the packet
    ) exmem_wb_pipe (
        .din_packet(exout_wb_packet),   // Input write-back packet from EX stage
        .clk(clk),                      // Clock signal
        .resetn(resetn),                // Active low reset signal
        .stall(stall_exmem),            // Stall signal for EX -> MEM pipeline
        .dout_packet(ex2mem_wb_packet)  // Output write-back packet to MEM stage
    );

    pipe #(
        .PTYPE(rv32_mem_packet_t) // Specify the type of the packet
    ) exmem_mem_pipe (
        .din_packet(exout_mem_packet),  // Input memory packet from EX stage
        .clk(clk),                      // Clock signal
        .resetn(resetn),                // Active low reset signal
        .stall(stall_exmem),            // Stall signal for EX -> MEM pipeline
        .dout_packet(ex2mem_mem_packet) // Output memory packet to MEM stage
    );

    pipe #(
        .PTYPE(rv32_ex_control_packet_t) // Specify the type of the packet
    ) exmem_ctrl_pipe (
        .din_packet(exout_control_packet), // Input control packet from EX stage
        .clk(clk),                         // Clock signal
        .resetn(resetn),                   // Active low reset signal
        .stall(stall_exmem),               // Stall signal for EX -> MEM pipeline
        .dout_packet(ex2mem_control_packet) // Output control packet to MEM stage
    );

    // ***********************************************************************
    // Memory Stage
    // ***********************************************************************
    // Handles memory operations and prepares data for write-back
    mem_stage mem_stage_inst (
        .clk(clk),                          // Clock signal
        .resetn(resetn),                    // Active low reset signal
        .wb_in_packet(ex2mem_wb_packet),    // Input write-back packet from EX stage
        .control_packet(ex2mem_control_packet), // Input control packet from EX stage
        .mem_packet(ex2mem_mem_packet),     // Input memory access packet from EX stage
        .wb_out_packet(mem2wb_packet)       // Output write-back packet to WB stage
    );

    // Pipeline: MEM -> WB
    // Transfers results from the Memory stage to the Write-Back stage
    pipe #(
        .PTYPE(rv32_mem2wb_packet_t) // Specify the type of the packet
    ) mem_wb_pipe (
        .din_packet(mem2wb_packet),   // Input write-back packet from MEM stage
        .clk(clk),                    // Clock signal
        .resetn(resetn),              // Active low reset signal
        .stall(stall_memwb),          // Stall signal for MEM -> WB pipeline
        .dout_packet(wb_out_packet)   // Output write-back packet to WB stage
    );

    // ***********************************************************************
    // Register File Stage
    // ***********************************************************************
    // Handles register file operations and instruction commit
    regfile_stage regfile_inst (
        .clk(clk),                          // Clock signal
        .resetn(resetn),                    // Active low reset signal
        .instruction_packet(of_packet_out), // Input instruction packet from OF stage
        .writeback_packet(wb_out_packet),   // Input write-back packet from MEM stage
        .issue_packet(regfile_in_packet_out), // Output packet to EX stage
        .instruction_commit(instruction_commit) // Signal indicating instruction commit
    );

endmodule