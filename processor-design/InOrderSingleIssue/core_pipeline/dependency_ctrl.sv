// ============================================================================
//  Module:      dependency_ctrl
//  Description: Data hazard detection and forwarding control logic for a simple
//               in-order, single-issue RISC-V pipeline. Handles forwarding and
//               stalling for RAW hazards between pipeline stages.
//  Author:      Bhanu Pande
//  Date:        [Date]
//  Revision:    1.0
// ============================================================================

import rv32_pkg::*; // Import the package for constants and types

module dependency_ctrl (
    input  logic clk,
    input  logic resetn,
    input  logic dmem_ready,       // Data Memory ready signal
    input  logic imem_ready,       // Instruction Memory ready signal
    input  rv32_instr_packet_t    ofout_packet,      // Output from OF stage
    input  rv32_ex2mem_wb_packet_t exout_wb_packet,  // Output from EX stage
    input  rv32_mem_packet_t      exout_mem_packet,  // Output from EX/MEM stage (for load/store)
    input  rv32_mem2wb_packet_t   memout_packet,     // Output from MEM stage
    input  rv32_mem2wb_packet_t   wbout_packet,      // Output from WB stage
    output rv32_fwd_packet_t      fwd_packet,        // Forwarding data/control signals
    output logic                  stall_if,          // Stall signal for IF stage
    output logic                  stall_ifof,        // Stall signal for IF/OF pipeline register
    output logic                  stall_ofex,        // Stall signal for OF/EX pipeline register
    output logic                  stall_exmem,       // Stall signal for EX/MEM pipeline register
    output logic                  stall_memwb        // Stall signal for MEM/WB pipeline register
);

    // =========================================================================
    // Local Parameters and Signal Declarations
    // =========================================================================
    localparam NOP = 32'h00000013; // NOP instruction encoding

    // Register source fields from OF stage
    logic [4:0] rs1_ofoutstg;
    logic [4:0] rs2_ofoutstg;

    // Hazard detection signals
    logic rs_ofoutstg_matches_load_addr;
    logic rs1_ofoutstg_matches_rd_exoutstg;
    logic rs2_ofoutstg_matches_rd_exoutstg;
    logic rs1_ofoutstg_matches_rd_memoutstg;
    logic rs2_ofoutstg_matches_rd_memoutstg;
    logic rs1_ofoutstg_matches_rd_wboutstg;
    logic rs2_ofoutstg_matches_rd_wboutstg;

    // Forwarding addresses and data from pipeline stages
    logic [4:0]  fwd_addr_exoutstg;
    logic [4:0]  fwd_addr_memoutstg;
    logic [4:0]  fwd_addr_wboutstg;
    logic [31:0] fwd_data_exoutstg;
    logic [31:0] fwd_data_memoutstg;
    logic [31:0] fwd_data_wboutstg;

    // Forwarding enables from pipeline stages
    logic fwd_enable_exoutstg;
    logic fwd_enable_memoutstg;
    logic fwd_enable_wboutstg;

    // Forwarding selection vector
    logic [5:0] fwd_packet_sel;

    // Valid opcode signals for each stage
    logic of_valid_opcode;
    logic ex_valid_opcode;
    logic mem_valid_opcode;
    logic wb_valid_opcode;

    // Load/store hazard detection
    logic rs1_ofoutstg_matches_exlsaddr;
    logic rs2_ofoutstg_matches_exlsaddr;

    // =========================================================================
    // Hazard and Forwarding Detection Logic
    // =========================================================================

    // Detect if OF stage rs1/rs2 matches EX stage load/store address
    assign rs1_ofoutstg_matches_exlsaddr = (rs1_ofoutstg == exout_mem_packet.addr) && of_valid_opcode && (exout_mem_packet.is_load || exout_mem_packet.is_store);
    assign rs2_ofoutstg_matches_exlsaddr = (rs2_ofoutstg == exout_mem_packet.addr) && of_valid_opcode && (exout_mem_packet.is_load || exout_mem_packet.is_store);

    // Valid opcode signals (ignore instructions marked as dont_forward)
    assign of_valid_opcode  = ~ofout_packet.dont_forward && ofout_packet.valid_opcode;
    assign ex_valid_opcode  = ~exout_wb_packet.dont_forward && exout_wb_packet.valid_opcode;
    assign mem_valid_opcode = ~memout_packet.dont_forward && memout_packet.valid_opcode;
    assign wb_valid_opcode  = ~wbout_packet.dont_forward && wbout_packet.valid_opcode;

    // Register source selections from OF stage
    assign rs1_ofoutstg = ofout_packet.rs1_sel;
    assign rs2_ofoutstg = ofout_packet.rs2_sel;
    
    // Forwarding addresses from each stage
    assign fwd_addr_exoutstg  = exout_wb_packet.wb_addr;
    assign fwd_addr_memoutstg = memout_packet.wb_addr;
    assign fwd_addr_wboutstg  = wbout_packet.wb_addr;

    // Forwarding data from each stage
    assign fwd_data_exoutstg  = exout_wb_packet.wb_data;
    assign fwd_data_memoutstg = memout_packet.wb_data;
    assign fwd_data_wboutstg  = wbout_packet.wb_data;

    // Forwarding enables from each stage
    assign fwd_enable_exoutstg  = exout_wb_packet.wb_enable;
    assign fwd_enable_memoutstg = memout_packet.wb_enable;
    assign fwd_enable_wboutstg  = wbout_packet.wb_enable;

    // Detect RAW hazards for rs1/rs2 with EX, MEM, WB stages
    assign rs1_ofoutstg_matches_rd_exoutstg  = (rs1_ofoutstg == fwd_addr_exoutstg)  && of_valid_opcode && ex_valid_opcode;
    assign rs2_ofoutstg_matches_rd_exoutstg  = (rs2_ofoutstg == fwd_addr_exoutstg)  && of_valid_opcode && ex_valid_opcode;
    assign rs1_ofoutstg_matches_rd_memoutstg = (rs1_ofoutstg == fwd_addr_memoutstg) && of_valid_opcode && mem_valid_opcode;
    assign rs2_ofoutstg_matches_rd_memoutstg = (rs2_ofoutstg == fwd_addr_memoutstg) && of_valid_opcode && mem_valid_opcode;
    assign rs1_ofoutstg_matches_rd_wboutstg  = (rs1_ofoutstg == fwd_addr_wboutstg)  && of_valid_opcode && wb_valid_opcode;
    assign rs2_ofoutstg_matches_rd_wboutstg  = (rs2_ofoutstg == fwd_addr_wboutstg)  && of_valid_opcode && wb_valid_opcode;

    // Forwarding selection vector (bitwise encoding of matches)
    assign fwd_packet_sel = {rs2_ofoutstg_matches_rd_exoutstg, rs1_ofoutstg_matches_rd_exoutstg,
                             rs2_ofoutstg_matches_rd_memoutstg, rs1_ofoutstg_matches_rd_memoutstg,
                             rs2_ofoutstg_matches_rd_wboutstg, rs1_ofoutstg_matches_rd_wboutstg};

    // =========================================================================
    // Forwarding Mux Logic
    // =========================================================================
    // Selects the correct forwarding data for rs1 and rs2 based on detected hazards.
    always_ff @(posedge clk or negedge resetn) begin
        if (~resetn) begin
            fwd_packet.fwd_rs1_data   <= 32'h0;
            fwd_packet.fwd_rs2_data   <= 32'h0;
            fwd_packet.fwd_rs1_enable <= 1'b0;
            fwd_packet.fwd_rs2_enable <= 1'b0;
        // If the data memory (dmem) is ready, execute the corresponding logic for memory operations.
        // This condition typically handles the case where a memory access has completed and the pipeline can proceed.
        end else if (dmem_ready) begin
            casex (fwd_packet_sel)
                // Forward from EX stage to both rs1 and rs2
                6'b11xxxx: begin
                    fwd_packet.fwd_rs1_data   <= fwd_data_exoutstg;
                    fwd_packet.fwd_rs1_enable <= fwd_enable_exoutstg;
                    fwd_packet.fwd_rs2_data   <= fwd_data_exoutstg;
                    fwd_packet.fwd_rs2_enable <= fwd_enable_exoutstg;
                end
                // Forward from MEM to rs1, EX to rs2
                6'b10x1xx: begin
                    fwd_packet.fwd_rs1_data   <= fwd_data_memoutstg;
                    fwd_packet.fwd_rs1_enable <= fwd_enable_memoutstg;
                    fwd_packet.fwd_rs2_data   <= fwd_data_exoutstg;
                    fwd_packet.fwd_rs2_enable <= fwd_enable_exoutstg;
                end
                // Forward from WB to rs1, EX to rs2
                6'b10x0x1: begin
                    fwd_packet.fwd_rs1_data   <= fwd_data_wboutstg;
                    fwd_packet.fwd_rs1_enable <= fwd_enable_wboutstg;
                    fwd_packet.fwd_rs2_data   <= fwd_data_exoutstg;
                    fwd_packet.fwd_rs2_enable <= fwd_enable_exoutstg;
                end
                // Forward from EX to rs2 only
                6'b10x0x0: begin
                    fwd_packet.fwd_rs2_data   <= fwd_data_exoutstg;
                    fwd_packet.fwd_rs2_enable <= fwd_enable_exoutstg;
                end
                // Forward from EX to rs1, MEM to rs2
                6'b011xxx: begin
                    fwd_packet.fwd_rs1_data   <= fwd_data_exoutstg;
                    fwd_packet.fwd_rs1_enable <= fwd_enable_exoutstg;
                    fwd_packet.fwd_rs2_data   <= fwd_data_memoutstg;
                    fwd_packet.fwd_rs2_enable <= fwd_enable_memoutstg;
                end
                // Forward from EX to rs1, WB to rs2
                6'b010x1x: begin
                    fwd_packet.fwd_rs1_data   <= fwd_data_exoutstg;
                    fwd_packet.fwd_rs1_enable <= fwd_enable_exoutstg;
                    fwd_packet.fwd_rs2_data   <= fwd_data_wboutstg;
                    fwd_packet.fwd_rs2_enable <= fwd_enable_wboutstg;
                end
                // Forward from EX to rs1 only
                6'b010x0x: begin
                    fwd_packet.fwd_rs1_data   <= fwd_data_exoutstg;
                    fwd_packet.fwd_rs1_enable <= fwd_enable_exoutstg;
                end
                // Forward from MEM to both rs1 and rs2
                6'b0011xx: begin
                    fwd_packet.fwd_rs1_data   <= fwd_data_memoutstg;
                    fwd_packet.fwd_rs1_enable <= fwd_enable_memoutstg;
                    fwd_packet.fwd_rs2_data   <= fwd_data_memoutstg;
                    fwd_packet.fwd_rs2_enable <= fwd_enable_memoutstg;
                end
                // Forward from WB to rs1, MEM to rs2
                6'b0010x1: begin
                    fwd_packet.fwd_rs1_data   <= fwd_data_wboutstg;
                    fwd_packet.fwd_rs1_enable <= fwd_enable_wboutstg;
                    fwd_packet.fwd_rs2_data   <= fwd_data_memoutstg;
                    fwd_packet.fwd_rs2_enable <= fwd_enable_memoutstg;
                end
                // Forward from MEM to rs2 only
                6'b0010x0: begin
                    fwd_packet.fwd_rs2_data   <= fwd_data_memoutstg;
                    fwd_packet.fwd_rs2_enable <= fwd_enable_memoutstg;
                end
                // Forward from MEM to rs1, WB to rs2
                6'b00011x: begin
                    fwd_packet.fwd_rs1_data   <= fwd_data_memoutstg;
                    fwd_packet.fwd_rs1_enable <= fwd_enable_memoutstg;
                    fwd_packet.fwd_rs2_data   <= fwd_data_wboutstg;
                    fwd_packet.fwd_rs2_enable <= fwd_enable_wboutstg;
                end
                // Forward from MEM to rs1 only
                6'b00010x: begin
                    fwd_packet.fwd_rs1_data   <= fwd_data_memoutstg;
                    fwd_packet.fwd_rs1_enable <= fwd_enable_memoutstg;
                end
                // Forward from WB to both rs1 and rs2
                6'b000011: begin
                    fwd_packet.fwd_rs1_data   <= fwd_data_wboutstg;
                    fwd_packet.fwd_rs1_enable <= fwd_enable_wboutstg;
                    fwd_packet.fwd_rs2_data   <= fwd_data_wboutstg;
                    fwd_packet.fwd_rs2_enable <= fwd_enable_wboutstg;
                end
                // Forward from WB to rs2 only
                6'b000010: begin
                    fwd_packet.fwd_rs2_data   <= fwd_data_wboutstg;
                    fwd_packet.fwd_rs2_enable <= fwd_enable_wboutstg;
                end
                // Forward from WB to rs1 only
                6'b000001: begin
                    fwd_packet.fwd_rs1_data   <= fwd_data_wboutstg;
                    fwd_packet.fwd_rs1_enable <= fwd_enable_wboutstg;
                end
                // No forwarding needed: keep previous data, disable enables
                default: begin
                    fwd_packet.fwd_rs1_data   <= fwd_packet.fwd_rs1_data;
                    fwd_packet.fwd_rs2_data   <= fwd_packet.fwd_rs2_data;
                    fwd_packet.fwd_rs1_enable <= 1'b0;
                    fwd_packet.fwd_rs2_enable <= 1'b0;
                end
            endcase
        end
    end

    // =========================================================================
    // Stall Logic
    // =========================================================================
    // Stall if OF stage needs data from a load in EX stage (RAW hazard)
    always_comb begin
        // Assert stall if either rs1 or rs2 in OF matches EX load/store address and EX is a load
        stall_ifof = ((rs1_ofoutstg_matches_exlsaddr || rs2_ofoutstg_matches_exlsaddr) &&
                     exout_mem_packet.is_load) || ~dmem_ready || ~imem_ready;
        stall_if   = ((rs1_ofoutstg_matches_exlsaddr || rs2_ofoutstg_matches_exlsaddr) &&
                     exout_mem_packet.is_load) || ~dmem_ready;
        stall_ofex = ~dmem_ready;
        stall_exmem = ~dmem_ready;
        stall_memwb = ~dmem_ready;
    end

endmodule