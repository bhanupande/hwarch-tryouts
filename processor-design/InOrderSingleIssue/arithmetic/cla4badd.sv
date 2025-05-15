import rv32_pkg::*; // Import package for cla function
module cla4badd (
    input logic [3:0] a, // 4-bit input operand a
    input logic [3:0] b, // 4-bit input operand b
    input logic       cin, // Carry input
    output logic [4:0] sum, // 5-bit output sum (4 bits + carry)
    output logic       cout // Carry output
);
    logic [3:0] [2:0] cla_int; // Carry lookahead signals
    logic [4:0] cint;
    assign sum[4] = cint[4];
    assign cout = cint[4];
    assign cint[0] = cin;
    assign cint[1] = cla_int[0][1] | (cla_int[0][0] & cint[0]);
    assign cint[2] = cla_int[1][1] |
                    (cla_int[1][0] & cla_int[0][1]) |
                    (cla_int[1][0] & cla_int[0][0] & cint[0]);
    assign cint[3] = cla_int[2][1] |
                    (cla_int[2][0] & cla_int[1][1]) |
                    (cla_int[2][0] & cla_int[1][0] & cla_int[0][1]) |
                    (cla_int[2][0] & cla_int[1][0] & cla_int[0][0] & cint[0]);
    assign cint[4] = cla_int[3][1] |
                    (cla_int[3][0] & cla_int[2][1]) |
                    (cla_int[3][0] & cla_int[2][0] & cla_int[1][1]) |
                    (cla_int[3][0] & cla_int[2][0] & cla_int[1][0] & cla_int[0][1]) |
                    (cla_int[3][0] & cla_int[2][0] & cla_int[1][0] & cla_int[0][0] & cint[0]);
    generate
        for (genvar i=0; i<4; i++) begin : gen_cla_int
            assign cla_int[i][2:0] = cla(a[i], b[i], cint[i]);
            assign sum[i] = cla_int[i][2];
        end
    endgenerate

endmodule
