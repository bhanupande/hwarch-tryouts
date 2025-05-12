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
    rv32_if_packet_t if_packet_out;             // Output instruction packet from instruction fetch stage
    rv32_if_packet_t of_packet_in;              // Input instruction packet to the Operand Fetch stage
    rv32_instr_packet_t of_packet_out;          // Output instruction packet from Operand Fetch stage
    rv32_issue_packet_t regfile_in_packet_out;  // Output instruction packet from Operand Fetch stage
    rv32_issue_packet_t ex_packet_in;           // Input instruction packet to the Execute stage
    rv32_branch_packet_t ex2if_branch_packet;   // Branch packet output
    rv32_mem_packet_t exout_mem_packet;         // Memory access packet output
    rv32_mem_packet_t ex2mem_mem_packet;        // Memory access packet output
    rv32_ex2mem_wb_packet_t exout_wb_packet;    // Write-back packet output
    rv32_ex2mem_wb_packet_t ex2mem_wb_packet;   // Write-back packet output
    rv32_ex_control_packet_t exout_control_packet; // Control signals for memory operations
    rv32_ex_control_packet_t ex2mem_control_packet; // Control signals for memory operations
    rv32_mem2wb_packet_t mem2wb_packet;         // Write-back packet output
    rv32_mem2wb_packet_t wb_out_packet;         // Write-back packet output

    // ***********************************************************************
    // Instruction Fetch Stage
    // ***********************************************************************
    if_stage if_stage_inst (
        .clk(clk),
        .resetn(resetn),
        .branch_packet(ex2if_branch_packet), // Input branch packet
        .stall_fetch(1'b0),                  // No stall in this example
        .if_packet_out(if_packet_out)        // Output instruction packet
    );

    // Pipeline: IF -> OF
    pipe #(
        .PTYPE(rv32_if_packet_t) // Specify the type of the packet
    ) ifof_pipe (
        .din_packet(if_packet_out), // Input packet from if_stage
        .clk(clk),                  // Clock signal
        .resetn(resetn),            // Active low reset signal
        .stall(1'b0),               // No stall in this example
        .dout_packet(of_packet_in)  // Output packet
    );

    // ***********************************************************************
    // Operand Fetch Stage
    // ***********************************************************************
    of_stage of_stage_inst (
        .if_packet(of_packet_in),         // Input instruction packet from the pipeline
        .instruction_packet(of_packet_out) // Output packet
    );

    // Pipeline: OF -> EX
    pipe #(
        .PTYPE(rv32_issue_packet_t) // Specify the type of the packet
    ) ofex_pipe (
        .din_packet(regfile_in_packet_out), // Input packet from of_stage
        .clk(clk),                          // Clock signal
        .resetn(resetn),                    // Active low reset signal
        .stall(1'b0),                       // No stall in this example
        .dout_packet(ex_packet_in)          // Output packet
    );

    // ***********************************************************************
    // Execute Stage
    // ***********************************************************************
    execute_stage ex_stage_inst (
        .issued_instruction_packet(ex_packet_in), // Input instruction packet from the pipeline
        .branch_packet(ex2if_branch_packet),      // Output branch packet
        .mem_packet(exout_mem_packet),            // Output memory access packet
        .wb_packet(exout_wb_packet),              // Output write-back packet
        .ex_control_packet(exout_control_packet)  // Output control packet
    );

    // Pipelines: EX -> MEM
    pipe #(
        .PTYPE(rv32_ex2mem_wb_packet_t) // Specify the type of the packet
    ) exmem_wb_pipe (
        .din_packet(exout_wb_packet), // Input packet from ex_stage
        .clk(clk),                    // Clock signal
        .resetn(resetn),              // Active low reset signal
        .stall(1'b0),                 // No stall in this example
        .dout_packet(ex2mem_wb_packet) // Output packet
    );

    pipe #(
        .PTYPE(rv32_mem_packet_t) // Specify the type of the packet
    ) exmem_mem_pipe (
        .din_packet(exout_mem_packet), // Input packet from ex_stage
        .clk(clk),                     // Clock signal
        .resetn(resetn),               // Active low reset signal
        .stall(1'b0),                  // No stall in this example
        .dout_packet(ex2mem_mem_packet) // Output packet
    );

    pipe #(
        .PTYPE(rv32_ex_control_packet_t) // Specify the type of the packet
    ) exmem_ctrl_pipe (
        .din_packet(exout_control_packet), // Input packet from ex_stage
        .clk(clk),                         // Clock signal
        .resetn(resetn),                   // Active low reset signal
        .stall(1'b0),                      // No stall in this example
        .dout_packet(ex2mem_control_packet) // Output packet
    );

    // ***********************************************************************
    // Memory Stage
    // ***********************************************************************
    mem_stage mem_stage_inst (
        .clk(clk),                          // Clock signal
        .resetn(resetn),                    // Active low reset signal
        .wb_in_packet(ex2mem_wb_packet),    // Input write-back packet
        .control_packet(ex2mem_control_packet), // Input control packet
        .mem_packet(ex2mem_mem_packet),     // Input memory access packet
        .wb_out_packet(mem2wb_packet)       // Output write-back packet
    );

    // Pipeline: MEM -> WB
    pipe #(
        .PTYPE(rv32_mem2wb_packet_t) // Specify the type of the packet
    ) mem_wb_pipe (
        .din_packet(mem2wb_packet), // Input packet from mem_stage
        .clk(clk),                  // Clock signal
        .resetn(resetn),            // Active low reset signal
        .stall(1'b0),               // No stall in this example
        .dout_packet(wb_out_packet) // Output packet
    );

    // ***********************************************************************
    // Register File Stage
    // ***********************************************************************
    regfile_stage regfile_inst (
        .clk(clk),                          // Clock signal
        .resetn(resetn),                    // Active low reset signal
        .instruction_packet(of_packet_out), // Input instruction packet from the pipeline
        .writeback_packet(wb_out_packet),   // Input write-back packet
        .issue_packet(regfile_in_packet_out) // Output packet for the next stage
    );

endmodule