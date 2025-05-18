`timescale 1ns/1ps

module gen_xifo_tb;

    // Parameters
    parameter DATA_WIDTH = 32;
    parameter DEPTH = 16;
    parameter Mode = "LIFO"; // FIFO or LIFO
    parameter NUM_TRANSACTIONS = 1000;

    // DUT signals
    logic clk, rst_n;
    logic push, pop;
    logic [DATA_WIDTH-1:0] din, dout;
    logic full, empty;

    // Reference model
    logic [DATA_WIDTH-1:0] ref_mem [0:DEPTH-1];
    int ref_head, ref_tail, ref_count;

    // Randomization
    logic [DATA_WIDTH-1:0] rand_data;
    int tx_sent, tx_recv, errors;

    logic [DATA_WIDTH-1:0] expected, received;

    // Instantiate DUT
    mem_ctrl #(
        .DEPTH(DEPTH),
        .WIDTH(DATA_WIDTH),
        .LATENCY(1) // No latency for this test
    ) dut (
        .clk(clk),
        .rstn(rst_n),
        .write_enable(push),
        .read_enable(pop),
        .write_addr(ref_tail),
        .read_addr(ref_head),
        .write_data(din),
        .mem_ready(),
        .read_data(dout)
    );
    //gen_xifo #(
    //    .DWidth(DATA_WIDTH),
    //    .QueueDepth(DEPTH),
    //    .Mode(Mode)
    //) dut (
    //    .clk(clk),
    //    .rstn(rst_n),
    //    .push(push),
    //    .pop(pop),
    //    .data_in(din),
    //    .data_out(dout),
    //    .full(full),
    //    .empty(empty)
    //);

    // Clock generation
    always #5 clk = ~clk;

    // Reset task
    task automatic reset_dut();
        rst_n = 0;
        push = 0;
        pop = 0;
        din = '0;
        @(negedge clk);
        @(negedge clk);
        rst_n = 1;
        @(negedge clk);
    endtask

    // Reference model push
    task automatic ref_push(input logic [DATA_WIDTH-1:0] data);
        if (ref_count < DEPTH) begin
            ref_mem[ref_tail] = data;
            ref_tail = (ref_tail + 1) % DEPTH;
            ref_count++;
        end
    endtask

    // Reference model pop
    function automatic logic [DATA_WIDTH-1:0] ref_pop();
        logic [DATA_WIDTH-1:0] data;
        data = 'x;
        if (ref_count > 0) begin
            data = ref_mem[ref_head];
            ref_head = (ref_head + 1) % DEPTH;
            ref_count--;
        end
        return data;
    endfunction

    // Expected value update
    // This is a simple way to keep track of the expected value
    //always @(posedge clk) begin
    //    if (pop) expected <= ref_pop();
    //end

    // Testbench main process
    initial begin
        clk = 0;
        reset_dut();

        ref_head = 0;
        ref_tail = 0;
        ref_count = 0;
        tx_sent = 0;
        tx_recv = 0;
        errors = 0;

        // Main stimulus loop
        while (tx_sent < NUM_TRANSACTIONS || tx_recv < NUM_TRANSACTIONS) begin
            @(negedge clk);

            // Randomly decide to push or pop
            push = 0;
            pop = 0;

            // Push logic
            if (tx_sent < NUM_TRANSACTIONS && !full && ($urandom_range(0,1) || empty)) begin
                rand_data = $urandom();
                din = rand_data;
                push = 1;
                ref_push(rand_data);
                tx_sent++;
            end

            // Pop logic
            if (!empty && (tx_recv < tx_sent) && ($urandom_range(0,1) || full)) begin
                pop = 1;
            end

            @(posedge clk);
            // Self-checking logic
            if (pop) begin
                received = dout;
                expected = ref_pop();
                tx_recv++;
                if (received !== expected) begin
                    $display("ERROR at %0t: Expected %h, got %h", $time, expected, received);
                    errors++;
                end
            end
        end

        // Final checks
        if (errors == 0 && tx_sent == tx_recv) begin
            $display("TEST PASSED: All data matched, no data loss.");
        end else begin
            $display("TEST FAILED: %0d errors, tx_sent=%0d, tx_recv=%0d", errors, tx_sent, tx_recv);
        end

        $finish;
    end

endmodule