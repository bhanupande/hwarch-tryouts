// ============================================================================
// 4-bit Carry Lookahead Adder (CLA) Module
// ----------------------------------------------------------------------------
// Filename    : cla4badd.sv
// Description : 4-bit adder using carry lookahead logic. Computes the sum and
//               carry-out for two 4-bit operands and a carry-in.
// Author      : Bhanu Pande
// Date        : 2025-05-16
// Dependencies: rv32_pkg (for cla function)
// ============================================================================

import rv32_pkg::*; // Import package for cla function

module cla4badd (
    input  logic [3:0] a,    // 4-bit input operand a
    input  logic [3:0] b,    // 4-bit input operand b
    input  logic       cin,  // Carry input
    output logic [3:0] sum,  // 4-bit output sum (4 bits + carry)
    output logic       cout  // Carry output
);

    // Internal signals for carry lookahead and carry chain
    logic [3:0] [2:0] cla_int; // Each element: [2]=sum, [1]=generate, [0]=propagate
    logic [4:0] cint;          // Carry chain (cint[0]=cin, cint[4]=final carry)

    // Assign carry-out and MSB of sum
    assign cout   = cint[4];

    // Carry chain initialization
    assign cint[0] = cin;

    // Carry lookahead logic for each bit position
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

    // Generate block for each bit: compute sum, generate, propagate using cla function
    generate
        for (genvar i=0; i<4; i++) begin : gen_cla_int
            assign cla_int[i][2:0] = cla(a[i], b[i], cint[i]); // [2]=sum, [1]=generate, [0]=propagate
            assign sum[i] = cla_int[i][2]; // Assign sum bit
        end
    endgenerate

endmodule
