//-----------------------------------------------------------------------------
// File: mem_stage.sv
// Description: This module implements the memory stage of a RISC-V processor.
//              It handles memory read and write operations and prepares data
//              for the write-back stage.
// Author: Bhanu Pande
// Date: May 12, 2025
//-----------------------------------------------------------------------------

import rv32_pkg::*; // Import the package for constants and types

module mem_stage (
    input logic clk,                              // Clock signal
    input logic resetn,                           // Active low reset signal
    input rv32_ex2mem_wb_packet_t wb_in_packet,   // Input write-back packet
    input rv32_ex_control_packet_t control_packet, // Input control packet
    input rv32_mem_packet_t mem_packet,           // Input memory access packet
    output rv32_mem2wb_packet_t wb_out_packet     // Output write-back packet
);

    // ***********************************************************************
    // Internal Signals
    // ***********************************************************************
    logic [31:0] mem_read_data;  // Data read from memory
    logic [31:0] load_data;      // Processed load data
    logic [31:0] mem_write_data; // Data to be written to memory
    logic mem_access;            // Memory access signal

    // ***********************************************************************
    // Memory Access Signal
    // ***********************************************************************
    assign mem_access = mem_packet.read_enable || mem_packet.write_enable; // Memory access is enabled for read or write

    // ***********************************************************************
    // Write-Back Packet Assignments
    // ***********************************************************************
    assign wb_out_packet.rs1_sel = wb_in_packet.rs1_sel; // Source register 1 selection
    assign wb_out_packet.rs2_sel = wb_in_packet.rs2_sel; // Source register 2 selection
    assign wb_out_packet.wb_pc = wb_in_packet.wb_pc; // Program counter for write-back
    assign wb_out_packet.wb_addr = wb_in_packet.wb_addr; // Register address to write back
    assign wb_out_packet.wb_data = mem_packet.read_enable ? load_data : wb_in_packet.wb_data; // Data to write back
    assign wb_out_packet.wb_enable = mem_packet.read_enable || wb_in_packet.wb_enable; // Enable write-back if memory read or previous stage enabled it

    // ***********************************************************************
    // Load and Store Data Processing
    // ***********************************************************************
    always_comb begin
        // Load data based on load type
        case (control_packet.load_type)
            3'b000: load_data = {{24{mem_read_data[7]}}, mem_read_data[7:0]};  // Load Byte (signed)
            3'b001: load_data = {{16{mem_read_data[15]}}, mem_read_data[15:0]}; // Load Halfword (signed)
            3'b010: load_data = mem_read_data;                                 // Load Word
            3'b011: load_data = {24'h0, mem_read_data[7:0]};                   // Load Byte (unsigned)
            3'b100: load_data = {16'h0, mem_read_data[15:0]};                  // Load Halfword (unsigned)
            default: load_data = '0;                                          // Default case
        endcase

        // Store data based on store type
        case (control_packet.store_type)
            2'b00: mem_write_data = {{24{mem_packet.data[7]}}, mem_packet.data[7:0]};  // Store Byte
            2'b01: mem_write_data = {{16{mem_packet.data[15]}}, mem_packet.data[15:0]}; // Store Halfword
            2'b10: mem_write_data = mem_packet.data;                                   // Store Word
            default: mem_write_data = '0;                                             // Default case
        endcase
    end

    // ***********************************************************************
    // Memory Module Instance
    // ***********************************************************************
    mem dmem (
        .clk(clk),                          // Clock signal
        .rstn(resetn),                      // Active low reset signal
        .write_enable(mem_packet.write_enable), // Enable write operation
        .read_enable(mem_packet.read_enable),   // Enable read operation
        .write_addr(mem_packet.addr),           // Write address
        .read_addr(mem_packet.addr),            // Read address (assuming word-aligned addresses)
        .write_data(mem_write_data),            // Data to write to memory
        .read_data(mem_read_data)               // Data read from memory
    );

endmodule