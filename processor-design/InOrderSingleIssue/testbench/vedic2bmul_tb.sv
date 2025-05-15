`timescale 1ns/1ps

module vedic2bmul_tb;

    // DUT inputs and outputs
    reg  [1:0] a, b;
    wire [3:0] prod;

    // Instantiate the DUT
    vedic2bmul dut (
        .a(a),
        .b(b),
        .o(prod)
    );

    // Test variables
    integer i;
    reg [3:0] expected;
    integer errors = 0;

    initial begin
        $display("Starting random test for vedic2bmul...");
        for (i = 0; i < 100; i = i + 1) begin
            // Generate random 2-bit numbers
            a = $urandom_range(0, 3);
            b = $urandom_range(0, 3);
            #1; // Wait for output to settle

            // Calculate expected result
            expected = a * b;

            // Self-check
            if (prod !== expected) begin
                $display("ERROR: a=%0d, b=%0d, prod=%0d, expected=%0d", a, b, prod, expected);
                errors = errors + 1;
            end else begin
                $display("PASS: a=%0d, b=%0d, prod=%0d", a, b, prod);
            end
            #4; // Wait before next input
        end

        if (errors == 0)
            $display("All tests passed!");
        else
            $display("Test completed with %0d errors.", errors);

        $finish;
    end

endmodule