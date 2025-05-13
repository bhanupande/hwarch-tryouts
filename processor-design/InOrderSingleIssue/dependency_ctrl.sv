import rv32_pkg::*; // Import the package for constants and types
module dependency_ctrl (
    input logic clk,
    input logic resetn,
    input rv32_if_packet_t ifout_packet,
    input rv32_if_packet_t ofin_packet,
    input rv32_instr_packet_t ofout_packet,
    input rv32_issue_packet_t exin_packet,
    input rv32_ex2mem_wb_packet_t exout_wb_packet,
    input rv32_ex2mem_wb_packet_t memin_wb_packet,
    input rv32_mem_packet_t memin_mem_packet,
    input rv32_ex_control_packet_t memin_control_packet,
    input rv32_mem2wb_packet_t memout_packet,
    input rv32_mem2wb_packet_t wbin_packet,
    output rv32_fwd_packet_t fwd_packet,
    output logic stall_if,
    output logic stall_ifof,
    output logic stall_ofex,
    output logic stall_exmem,
    output logic stall_memwb
);

    localparam NOP = 32'h00000013;
    logic of_valid_opcode;
    logic instr_meminstg_load;
    logic [4:0] instr_meminstg_load_reg;
    logic [31:0] instr_meminstg_load_addr;

    logic [4:0] rs1_ofoutstg;
    logic [4:0] rs2_ofoutstg;
    logic rs_ofoutstg_matches_load_addr;
    logic rs1_ofoutstg_matches_rd_exoutstg;
    logic rs2_ofoutstg_matches_rd_exoutstg;
    logic rs1_ofoutstg_matches_rd_memoutstg;
    logic rs2_ofoutstg_matches_rd_memoutstg;

    assign instr_meminstg_load = memin_mem_packet.read_enable && memin_wb_packet.wb_enable;
    assign instr_meminstg_load_addr = memin_mem_packet.addr;
    assign instr_meminstg_load_reg = memin_wb_packet.wb_addr;

    assign of_valid_opcode = ofout_packet.valid_opcode;
    assign ex_valid_opcode = exout_wb_packet.valid_opcode;
    assign mem_valid_opcode = memin_wb_packet.valid_opcode;

    assign rs1_ofoutstg = ofout_packet.rs1_sel;
    assign rs2_ofoutstg = ofout_packet.rs2_sel;

    assign rs1_ofoutstg_matches_load_addr = (rs1_ofoutstg == instr_meminstg_load_reg) && instr_meminstg_load && of_valid_opcode;
    assign rs2_ofoutstg_matches_load_addr = (rs2_ofoutstg == instr_meminstg_load_reg) && instr_meminstg_load && of_valid_opcode;

    assign rs1_ofoutstg_matches_rd_exoutstg = (rs1_ofoutstg == exout_wb_packet.wb_addr) && of_valid_opcode && ex_valid_opcode;
    assign rs2_ofoutstg_matches_rd_exoutstg = (rs2_ofoutstg == exout_wb_packet.wb_addr) && of_valid_opcode && ex_valid_opcode;

    assign rs1_ofoutstg_matches_rd_memoutstg = (rs1_ofoutstg == memin_wb_packet.wb_addr) && of_valid_opcode && mem_valid_opcode;
    assign rs2_ofoutstg_matches_rd_memoutstg = (rs2_ofoutstg == memin_wb_packet.wb_addr) && of_valid_opcode && mem_valid_opcode;

    always_ff @(posedge clk or negedge resetn) begin
        if (~resetn) begin
            fwd_packet.fwd_rs1_data <= 32'h0;
            fwd_packet.fwd_rs2_data <= 32'h0;
            fwd_packet.fwd_rs1_enable <= 1'b0;
            fwd_packet.fwd_rs2_enable <= 1'b0;
        end else begin
            case ({rs2_ofoutstg_matches_rd_exoutstg, rs1_ofoutstg_matches_rd_exoutstg, rs2_ofoutstg_matches_rd_memoutstg, rs1_ofoutstg_matches_rd_memoutstg})
                4'b0001: begin
                    fwd_packet.fwd_rs1_data     <= memin_wb_packet.wb_data;
                    fwd_packet.fwd_rs1_enable   <= memin_wb_packet.wb_enable;
                end
                4'b0010: begin
                    fwd_packet.fwd_rs2_data     <= memin_wb_packet.wb_data;
                    fwd_packet.fwd_rs2_enable   <= memin_wb_packet.wb_enable;
                end
                4'b0011: begin
                    fwd_packet.fwd_rs1_data     <= memin_wb_packet.wb_data;
                    fwd_packet.fwd_rs1_enable   <= memin_wb_packet.wb_enable;
                    fwd_packet.fwd_rs2_data     <= memin_wb_packet.wb_data;
                    fwd_packet.fwd_rs2_enable   <= memin_wb_packet.wb_enable;
                end
                4'b0100: begin
                    fwd_packet.fwd_rs1_data     <= exout_wb_packet.wb_data;
                    fwd_packet.fwd_rs1_enable   <= exout_wb_packet.wb_enable;
                end
                4'b0110: begin
                    fwd_packet.fwd_rs1_data     <= exout_wb_packet.wb_data;
                    fwd_packet.fwd_rs1_enable   <= exout_wb_packet.wb_enable;
                    fwd_packet.fwd_rs2_data     <= memin_wb_packet.wb_data;
                    fwd_packet.fwd_rs2_enable   <= memin_wb_packet.wb_enable;
                end
                4'b1000: begin
                    fwd_packet.fwd_rs2_data     <= exout_wb_packet.wb_data;
                    fwd_packet.fwd_rs2_enable   <= exout_wb_packet.wb_enable;
                end
                4'b1001: begin
                    fwd_packet.fwd_rs1_data     <= memin_wb_packet.wb_data;
                    fwd_packet.fwd_rs1_enable   <= memin_wb_packet.wb_enable;
                    fwd_packet.fwd_rs2_data     <= exout_wb_packet.wb_data;
                    fwd_packet.fwd_rs2_enable   <= exout_wb_packet.wb_enable;
                end
                4'b1100: begin
                    fwd_packet.fwd_rs1_data     <= exout_wb_packet.wb_data;
                    fwd_packet.fwd_rs1_enable   <= exout_wb_packet.wb_enable;
                    fwd_packet.fwd_rs2_data     <= exout_wb_packet.wb_data;
                    fwd_packet.fwd_rs2_enable   <= exout_wb_packet.wb_enable;
                end
                default: begin
                    fwd_packet.fwd_rs1_data <= fwd_packet.fwd_rs1_data;
                    fwd_packet.fwd_rs2_data <= fwd_packet.fwd_rs2_data;
                    fwd_packet.fwd_rs1_enable <= 1'b0;
                    fwd_packet.fwd_rs2_enable <= 1'b0;
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