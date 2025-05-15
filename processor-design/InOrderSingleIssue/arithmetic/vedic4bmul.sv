// ============================================================================
// 4-bit Vedic Multiplier Module
// ----------------------------------------------------------------------------
// Filename    : vedic_multiplier.sv
// Description : Implements a 4x4 Vedic multiplier using hierarchical 
//               decomposition and carry lookahead adders (CLA).
//               The design splits the 4-bit operands into 2-bit segments,
//               computes partial products using 2x2 Vedic multipliers, and
//               combines them using CLA-based adders for fast reduction.
// Author      : Bhanu Pande
// Date        : 2025-05-16
// Dependencies: rv32_pkg (for cla function), vedic2bmul, cla4badd
// ============================================================================

import rv32_pkg::*; // Import package for cla function

// -----------------------------------------------------------------------------
// Module:      vedic4bmul
// Description: 4x4 Vedic multiplier using 2x2 Vedic multipliers and CLA adders
// -----------------------------------------------------------------------------
module vedic4bmul (
    input  logic [3:0] a,      // 4-bit input operand a
    input  logic [3:0] b,      // 4-bit input operand b
    output logic [8:0] prod    // 9-bit product output (includes carry out)
);

    // Partial products from 2x2 multipliers
    logic [3:0] [3:0] partial_products; // Each 4-bit: output of vedic2bmul
    // Intermediate sums for reduction using CLA adders
    logic [2:0] [3:0] intermediate_sums;
    // Carry outputs from CLA adders
    logic [2:0] carry_out;

    // Operand splits for 2x2 multipliers
    logic [3:0] [1:0] aa; // Slices of a
    logic [3:0] [1:0] bb; // Slices of b

    // Assign lower and upper 2 bits of a and b for each partial product
    assign aa[0] = a[1:0]; // Lower 2 bits of a
    assign aa[1] = a[1:0]; // Lower 2 bits of a (for cross terms)
    assign aa[2] = a[3:2]; // Upper 2 bits of a
    assign aa[3] = a[3:2]; // Upper 2 bits of a (for cross terms)

    assign bb[0] = b[1:0]; // Lower 2 bits of b
    assign bb[1] = b[3:2]; // Upper 2 bits of b (for cross terms)
    assign bb[2] = b[1:0]; // Lower 2 bits of b (for cross terms)
    assign bb[3] = b[3:2]; // Upper 2 bits of b

    // Generate partial products using 2x2 Vedic multipliers
    generate
        for (genvar i=0; i<4; i++) begin : gen_partial_products
            vedic2bmul pp (
                .a(aa[i]),      // 2-bit slice of a
                .b(bb[i]),      // 2-bit slice of b
                .o(partial_products[i]) // 4-bit partial product output
            );
        end
    endgenerate

    // First CLA adder: add partial_products[1] and partial_products[2]
    cla4badd sum0 (
        .a(partial_products[1]),         // First partial product
        .b(partial_products[2]),         // Second partial product
        .cin(1'b0),                      // No carry-in for the first addition
        .sum(intermediate_sums[0]),      // First intermediate sum
        .cout(carry_out[0])              // Carry-out (not used in this stage)
    );

    // Second CLA adder: add upper bits of partial_products[0] and previous sum
    cla4badd sum1 (
        .a({2'b0, partial_products[0][3:2]}), // Upper 2 bits of first partial product, zero-extended
        .b(intermediate_sums[0]),              // First intermediate sum
        .cin(1'b0),                            // No carry-in
        .sum(intermediate_sums[1]),            // Second intermediate sum
        .cout(carry_out[1])                    // Carry-out (not used in this stage)
    );

    // Third CLA adder: add partial_products[3] and upper bits of previous sum
    cla4badd sum2 (
        .a(partial_products[3]),               // Last partial product
        .b({1'b0, |carry_out[1:0], intermediate_sums[1][3:2]}), // Combine carries and upper bits
        .cin(1'b0),                            // No carry-in
        .sum(intermediate_sums[2]),            // Final sum (upper 4 bits of product)
        .cout(carry_out[2])                    // Final carry-out (MSB of product)
    );

    // Concatenate all results to form the final 9-bit product
    assign prod[1:0] = partial_products[0][1:0];     // Lower 2 bits of the product
    assign prod[3:2] = intermediate_sums[1][1:0];    // Next 2 bits from intermediate sum
    assign prod[7:4] = intermediate_sums[2][3:0];    // Upper 4 bits from final sum
    assign prod[8]   = carry_out[2];                 // Final carry-out (MSB of the product)

endmodule