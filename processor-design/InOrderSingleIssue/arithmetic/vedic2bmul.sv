// -----------------------------------------------------------------------------
// Module:      vedic2bmul
// Description: 2-bit Vedic multiplier. Multiplies two 2-bit inputs (a, b)
//              and produces a 4-bit output (o). Uses half and full adders
//              for partial product summation.
// Author:      Bhanu Pande
// Date        : 2025-05-16
// Dependencies: rv32_pkg (for cla function)
// ----------------------------------------------------------------------------

import rv32_pkg::*; // Import package for half_add and full_add functions

module vedic2bmul (
    input  logic [1:0] a, // 2-bit input operand a
    input  logic [1:0] b, // 2-bit input operand b
    output logic [3:0] o  // 4-bit output product
);

    // Internal signals for partial products and intermediate sums
    logic a0b1;        // Partial product: a[0] & b[1]
    logic a1b0;        // Partial product: a[1] & b[0]
    logic a1b1;        // Partial product: a[1] & b[1]
    logic intermediate;// Carry output from half adder

    // Compute least significant bit of the product
    assign o[0] = a[0] & b[0];

    // Compute partial products for next stage
    assign a1b0 = a[1] & b[0];
    assign a0b1 = a[0] & b[1];
    assign a1b1 = a[1] & b[1];

    // Sum partial products using half adder for o[1] and intermediate carry
    assign {intermediate, o[1]} = half_add(a1b0, a0b1);

    // Use full adder for the most significant bits
    assign {o[3], o[2]} = half_add(a1b1, intermediate);

endmodule