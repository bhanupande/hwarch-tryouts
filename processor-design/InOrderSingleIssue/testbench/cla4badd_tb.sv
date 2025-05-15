`timescale 1ns/1ps

module cla4badd_tb;

    // DUT inputs and outputs
    logic [3:0] a, b;
    logic       cin;
    logic [4:0] sum;

    // Instantiate the DUT
    cla4badd dut (
        .a(a),
        .b(b),
        .cin(cin),
        .sum(sum),
        .cout(cout)
    );

    // Test variables
    integer i;
    reg [4:0] expected;
    integer errors = 0;

    initial begin
        $display("Starting random test for cla4badd...");
        for (i = 0; i < 100; i = i + 1) begin
            // Generate random 4-bit numbers
            a = $urandom_range(0, 15);
            b = $urandom_range(0, 15);
            cin = $urandom_range(0, 1);
            #1; // Wait for output to settle

            // Calculate expected result
            expected = a + b + cin;

            // Self-check
            if (sum !== expected) begin
                $display("ERROR: a=%0d, b=%0d, sum=%0d, expected=%0d", a, b, sum, expected);
                errors = errors + 1;
            end else begin
                $display("PASS: a=%0d, b=%0d, sum=%0d", a, b, sum);
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