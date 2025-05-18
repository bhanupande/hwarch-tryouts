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
    input rv32_ex2mem_wb_packet_t wb_in_packet,   // Input write-back packet from the execute stage
    input rv32_ex_control_packet_t control_packet, // Input control packet containing load/store type
    input rv32_mem_packet_t mem_packet,           // Input memory access packet with read/write details
    output logic dmem_ready,                     // Memory ready signal
    output rv32_mem2wb_packet_t wb_out_packet     // Output write-back packet for the next stage
);

    // ***********************************************************************
    // Internal Signals
    // ***********************************************************************
    logic [31:0] mem_read_data;  // Data read from memory
    logic [31:0] load_data;      // Processed load data based on load type
    logic [31:0] mem_write_data; // Data to be written to memory based on store type
    logic mem_access;            // Signal indicating if memory access is required

    // ***********************************************************************
    // Memory Access Signal
    // ***********************************************************************
    // Determine if memory access is required (either read or write)
    assign mem_access = mem_packet.read_enable || mem_packet.write_enable;

    // ***********************************************************************
    // Write-Back Packet Assignments
    // ***********************************************************************
    // Pass through or modify fields for the write-back stage
    assign wb_out_packet.dont_forward = wb_in_packet.dont_forward; // Propagate don't forward signal
    assign wb_out_packet.valid_opcode = wb_in_packet.valid_opcode; // Propagate valid opcode signal
    assign wb_out_packet.rs1_sel      = wb_in_packet.rs1_sel;      // Propagate source register 1 selection
    assign wb_out_packet.rs2_sel      = wb_in_packet.rs2_sel;      // Propagate source register 2 selection
    assign wb_out_packet.wb_pc        = wb_in_packet.wb_pc;        // Propagate program counter for write-back
    assign wb_out_packet.wb_addr      = wb_in_packet.wb_addr;      // Propagate register address for write-back

    // Select data for write-back: if load, use loaded data; otherwise, use ALU result
    assign wb_out_packet.wb_data      = mem_packet.read_enable ? load_data : wb_in_packet.wb_data;

    // Enable write-back if memory read or previous stage enabled it
    assign wb_out_packet.wb_enable    = mem_packet.read_enable || wb_in_packet.wb_enable;

    // Indicate if the operation is a load or store
    assign wb_out_packet.is_load      = mem_packet.is_load;
    assign wb_out_packet.is_store     = mem_packet.is_store;

    // ***********************************************************************
    // Load and Store Data Processing
    // ***********************************************************************
    // Process load data based on the load type specified in the control packet
    // and process store data based on the store type.
    always_comb begin
        // Load data selection based on load type
        case (control_packet.load_type)
            3'b000: load_data = {{24{mem_read_data[7]}}, mem_read_data[7:0]};    // Load Byte (signed)
            3'b001: load_data = {{16{mem_read_data[15]}}, mem_read_data[15:0]};  // Load Halfword (signed)
            3'b010: load_data = mem_read_data;                                   // Load Word
            3'b011: load_data = {24'h0, mem_read_data[7:0]};                     // Load Byte (unsigned)
            3'b100: load_data = {16'h0, mem_read_data[15:0]};                    // Load Halfword (unsigned)
            default: load_data = '0;                                             // Default case for invalid load type
        endcase

        // Store data selection based on store type
        case (control_packet.store_type)
            2'b00: mem_write_data = {{24{mem_packet.data[7]}}, mem_packet.data[7:0]};   // Store Byte
            2'b01: mem_write_data = {{16{mem_packet.data[15]}}, mem_packet.data[15:0]}; // Store Halfword
            2'b10: mem_write_data = mem_packet.data;                                    // Store Word
            default: mem_write_data = '0;                                               // Default case for invalid store type
        endcase
    end

    // ***********************************************************************
    // Memory Module Instance
    // ***********************************************************************
    // Instantiate the memory module for read and write operations.
    // The same address is used for both read and write (word-aligned).
    mem_ctrl dmem (
        .clk(clk),                              // Clock signal
        .rstn(resetn),                          // Active low reset signal
        .write_enable(mem_packet.write_enable), // Enable write operation
        .read_enable(mem_packet.read_enable),   // Enable read operation
        .write_addr(mem_packet.addr),           // Write address
        .read_addr(mem_packet.addr),            // Read address (assuming word-aligned addresses)
        .write_data(mem_write_data),            // Data to write to memory
        .mem_ready(dmem_ready),                 // Memory ready signal
        .read_data(mem_read_data)               // Data read from memory
    );

endmodule