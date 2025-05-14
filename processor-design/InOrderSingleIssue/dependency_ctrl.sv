import rv32_pkg::*; // Import the package for constants and types
module dependency_ctrl (
    input logic clk,
    input logic resetn,
    input rv32_if_packet_t ifout_packet,
    input rv32_instr_packet_t ofout_packet,
    input rv32_ex2mem_wb_packet_t exout_wb_packet,
    input rv32_ex2mem_wb_packet_t memin_wb_packet,
    input rv32_mem_packet_t memin_mem_packet,
    input rv32_ex_control_packet_t memin_control_packet,
    input rv32_mem2wb_packet_t memout_packet,
    input rv32_mem2wb_packet_t wbout_packet,
    output rv32_fwd_packet_t fwd_packet,
    output logic stall_if,
    output logic stall_ifof,
    output logic stall_ofex,
    output logic stall_exmem,
    output logic stall_memwb
);

    localparam NOP = 32'h00000013;
    logic [4:0] rs1_ofoutstg;
    logic [4:0] rs2_ofoutstg;
    logic rs_ofoutstg_matches_load_addr;
    logic rs1_ofoutstg_matches_rd_exoutstg;
    logic rs2_ofoutstg_matches_rd_exoutstg;
    logic rs1_ofoutstg_matches_rd_memoutstg;
    logic rs2_ofoutstg_matches_rd_memoutstg;
    logic rs1_ofoutstg_matches_rd_wboutstg;
    logic rs2_ofoutstg_matches_rd_wboutstg;

    logic [4:0] fwd_addr_exoutstg;
    logic [4:0] fwd_addr_memoutstg;
    logic [4:0] fwd_addr_wboutstg;

    logic [31:0] fwd_data_exoutstg;
    logic [31:0] fwd_data_memoutstg;
    logic [31:0] fwd_data_wboutstg;

    logic fwd_enable_exoutstg;
    logic fwd_enable_memoutstg;
    logic fwd_enable_wboutstg;

    logic [5:0] fwd_packet_sel;

    logic of_valid_opcode;
    logic ex_valid_opcode;
    logic mem_valid_opcode;
    logic wb_valid_opcode;

    assign of_valid_opcode  = ~ofout_packet.dont_forward && ofout_packet.valid_opcode;
    assign ex_valid_opcode  = ~exout_wb_packet.dont_forward && exout_wb_packet.valid_opcode;
    assign mem_valid_opcode = ~memout_packet.dont_forward && memout_packet.valid_opcode;
    assign wb_valid_opcode  = ~wbout_packet.dont_forward && wbout_packet.valid_opcode;

    assign rs1_ofoutstg = ofout_packet.rs1_sel;
    assign rs2_ofoutstg = ofout_packet.rs2_sel;
    
    assign fwd_addr_exoutstg = exout_wb_packet.wb_addr;
    assign fwd_addr_memoutstg = memout_packet.wb_addr;
    assign fwd_addr_wboutstg = wbout_packet.wb_addr;

    assign fwd_data_exoutstg = exout_wb_packet.wb_data;
    assign fwd_data_memoutstg = memout_packet.wb_data;
    assign fwd_data_wboutstg = wbout_packet.wb_data;

    assign fwd_enable_exoutstg = exout_wb_packet.wb_enable;
    assign fwd_enable_memoutstg = memout_packet.wb_enable;
    assign fwd_enable_wboutstg = wbout_packet.wb_enable;

    assign rs1_ofoutstg_matches_rd_exoutstg = (rs1_ofoutstg == fwd_addr_exoutstg) && of_valid_opcode && ex_valid_opcode;
    assign rs2_ofoutstg_matches_rd_exoutstg = (rs2_ofoutstg == fwd_addr_exoutstg) && of_valid_opcode && ex_valid_opcode;

    assign rs1_ofoutstg_matches_rd_memoutstg = (rs1_ofoutstg == fwd_addr_memoutstg) && of_valid_opcode && mem_valid_opcode;
    assign rs2_ofoutstg_matches_rd_memoutstg = (rs2_ofoutstg == fwd_addr_memoutstg) && of_valid_opcode && mem_valid_opcode;

    assign rs1_ofoutstg_matches_rd_wboutstg = (rs1_ofoutstg == fwd_addr_wboutstg) && of_valid_opcode && wb_valid_opcode;
    assign rs2_ofoutstg_matches_rd_wboutstg = (rs2_ofoutstg == fwd_addr_wboutstg) && of_valid_opcode && wb_valid_opcode;

    assign fwd_packet_sel = {rs2_ofoutstg_matches_rd_exoutstg, rs1_ofoutstg_matches_rd_exoutstg,
                             rs2_ofoutstg_matches_rd_memoutstg, rs1_ofoutstg_matches_rd_memoutstg,
                             rs2_ofoutstg_matches_rd_wboutstg, rs1_ofoutstg_matches_rd_wboutstg};

    always_ff @(posedge clk or negedge resetn) begin
        if (~resetn) begin
            fwd_packet.fwd_rs1_data             <= 32'h0;
            fwd_packet.fwd_rs2_data             <= 32'h0;
            fwd_packet.fwd_rs1_enable           <= 1'b0;
            fwd_packet.fwd_rs2_enable           <= 1'b0;
        end else begin
            casex (fwd_packet_sel)
                6'b11xxxx: begin
                    fwd_packet.fwd_rs1_data     <= fwd_data_exoutstg;
                    fwd_packet.fwd_rs1_enable   <= fwd_enable_exoutstg;
                    fwd_packet.fwd_rs2_data     <= fwd_data_exoutstg;
                    fwd_packet.fwd_rs2_enable   <= fwd_enable_exoutstg;
                end
                6'b10x1xx: begin
                    fwd_packet.fwd_rs1_data     <= fwd_data_memoutstg;
                    fwd_packet.fwd_rs1_enable   <= fwd_enable_memoutstg;
                    fwd_packet.fwd_rs2_data     <= fwd_data_exoutstg;
                    fwd_packet.fwd_rs2_enable   <= fwd_enable_exoutstg;
                end
                6'b10x0x1: begin
                    fwd_packet.fwd_rs1_data     <= fwd_data_wboutstg;
                    fwd_packet.fwd_rs1_enable   <= fwd_enable_wboutstg;
                    fwd_packet.fwd_rs2_data     <= fwd_data_exoutstg;
                    fwd_packet.fwd_rs2_enable   <= fwd_enable_exoutstg;
                end
                6'b10x0x0: begin
                    fwd_packet.fwd_rs2_data     <= fwd_data_exoutstg;
                    fwd_packet.fwd_rs2_enable   <= fwd_enable_exoutstg;
                end
                6'b011xxx: begin
                    fwd_packet.fwd_rs1_data     <= fwd_data_exoutstg;
                    fwd_packet.fwd_rs1_enable   <= fwd_enable_exoutstg;
                    fwd_packet.fwd_rs2_data     <= fwd_data_memoutstg;
                    fwd_packet.fwd_rs2_enable   <= fwd_enable_memoutstg;
                end
                6'b010x1x: begin
                    fwd_packet.fwd_rs1_data     <= fwd_data_exoutstg;
                    fwd_packet.fwd_rs1_enable   <= fwd_enable_exoutstg;
                    fwd_packet.fwd_rs2_data     <= fwd_data_wboutstg;
                    fwd_packet.fwd_rs2_enable   <= fwd_enable_wboutstg;
                end
                6'b010x0x: begin
                    fwd_packet.fwd_rs1_data     <= fwd_data_exoutstg;
                    fwd_packet.fwd_rs1_enable   <= fwd_enable_exoutstg;
                end
                6'b0011xx: begin
                    fwd_packet.fwd_rs1_data     <= fwd_data_memoutstg;
                    fwd_packet.fwd_rs1_enable   <= fwd_enable_memoutstg;
                    fwd_packet.fwd_rs2_data     <= fwd_data_memoutstg;
                    fwd_packet.fwd_rs2_enable   <= fwd_enable_memoutstg;
                end
                6'b0010x1: begin
                    fwd_packet.fwd_rs1_data     <= fwd_data_wboutstg;
                    fwd_packet.fwd_rs1_enable   <= fwd_enable_wboutstg;
                    fwd_packet.fwd_rs2_data     <= fwd_data_memoutstg;
                    fwd_packet.fwd_rs2_enable   <= fwd_enable_memoutstg;
                end
                6'b0010x0: begin
                    fwd_packet.fwd_rs2_data     <= fwd_data_memoutstg;
                    fwd_packet.fwd_rs2_enable   <= fwd_enable_memoutstg;
                end
                6'b00011x: begin
                    fwd_packet.fwd_rs1_data     <= fwd_data_memoutstg;
                    fwd_packet.fwd_rs1_enable   <= fwd_enable_memoutstg;
                    fwd_packet.fwd_rs2_data     <= fwd_data_wboutstg;
                    fwd_packet.fwd_rs2_enable   <= fwd_enable_wboutstg;
                end
                6'b00010x: begin
                    fwd_packet.fwd_rs1_data     <= fwd_data_memoutstg;
                    fwd_packet.fwd_rs1_enable   <= fwd_enable_memoutstg;
                end
                6'b000011: begin
                    fwd_packet.fwd_rs1_data     <= fwd_data_wboutstg;
                    fwd_packet.fwd_rs1_enable   <= fwd_enable_wboutstg;
                    fwd_packet.fwd_rs2_data     <= fwd_data_wboutstg;
                    fwd_packet.fwd_rs2_enable   <= fwd_enable_wboutstg;
                end
                6'b000010: begin
                    fwd_packet.fwd_rs2_data     <= fwd_data_wboutstg;
                    fwd_packet.fwd_rs2_enable   <= fwd_enable_wboutstg;
                end
                6'b000001: begin
                    fwd_packet.fwd_rs1_data     <= fwd_data_wboutstg;
                    fwd_packet.fwd_rs1_enable   <= fwd_enable_wboutstg;
                end
                default: begin
                    fwd_packet.fwd_rs1_data     <= fwd_packet.fwd_rs1_data;
                    fwd_packet.fwd_rs2_data     <= fwd_packet.fwd_rs2_data;
                    fwd_packet.fwd_rs1_enable   <= 1'b0;
                    fwd_packet.fwd_rs2_enable   <= 1'b0;
                end
            endcase
        end
    end

    always_comb begin
        stall_memwb = 1'b0;
        stall_exmem = stall_memwb;
        stall_ofex = stall_exmem || stall_memwb;
        stall_ifof = stall_ofex || stall_exmem || stall_memwb;
        stall_if = stall_ifof || stall_ofex || stall_exmem || stall_memwb;
    end

endmodule