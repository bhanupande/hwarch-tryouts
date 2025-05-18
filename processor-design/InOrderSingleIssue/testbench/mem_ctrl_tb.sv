`timescale 1ns/1ps

module mem_ctrl_tb;

    // Parameters
    parameter DATA_WIDTH = 32;
    parameter DEPTH = 16;
    parameter Mode = "LIFO"; // FIFO or LIFO
    parameter NUM_TRANSACTIONS = 1000;
    parameter LATENCY = 0; // No latency for this test

    // DUT signals
    logic clk, rst_n;
    logic push, pop;
    logic [DATA_WIDTH-1:0] din, dout;
    logic full, empty;
    logic mem_ready;

    // Reference model
    logic [DATA_WIDTH-1:0] ref_mem [0:DEPTH-1];
    bit   written_mask [0:DEPTH-1]; // Track which addresses have valid data

    // Randomization
    logic [DATA_WIDTH-1:0] rand_data;
    int tx_sent, tx_recv, errors;

    logic [DATA_WIDTH-1:0] expected, received;

    // Address pointers
    int ref_head, ref_tail;

    // Instantiate DUT
    mem_ctrl #(
        .DEPTH(DEPTH),
        .WIDTH(DATA_WIDTH),
        .LATENCY(LATENCY) // No latency for this test
    ) dut (
        .clk(clk),
        .rstn(rst_n),
        .write_enable(push),
        .read_enable(pop),
        .write_addr(ref_tail),
        .read_addr(ref_head),
        .write_data(din),
        .mem_ready(mem_ready),
        .read_data(dout)
    );

    // Clock generation
    always #5 clk = ~clk;

    // Test process
    initial begin
        clk = 0;
        rst_n = 0;
        push = 0;
        pop = 0;
        din = 0;
        ref_head = 0;
        ref_tail = 0;
        tx_sent = 0;
        tx_recv = 0;
        errors = 0;
        for (int i = 0; i < DEPTH; i++) begin
            ref_mem[i] = '0;
            written_mask[i] = 0;
        end

        // Reset sequence
        repeat (3) @(posedge clk);
        rst_n = 1;
        repeat (3) @(posedge clk);

        // -------------------------------
        // Read phase: Read from all addresses
        // -------------------------------
        @(negedge clk);
        for (int addr = 0; addr < DEPTH; addr++) begin
            push = 0;
            pop = 1;
            ref_head = addr;
            // Wait for mem_ready
            do @(negedge clk); while (!mem_ready);
            expected = ref_mem[addr];
            received = dout;
            if (received !== expected) begin
                $display("ERROR: Read addr=%0d, expected=0x%08x, got=0x%08x", addr, expected, received);
                errors++;
            end
            pop = 0;
        end

        // Final report
        $display("Test completed: errors=%0d", errors);
        if (errors == 0)
            $display("PASS: All transactions matched reference model.");
        else
            $display("FAIL: %0d errors detected.", errors);

        $finish;
    end

    // -------------------------------
    // Write phase: Write to all addresses
    // -------------------------------
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Reset logic
            push <= 0;
            pop <= 0;
            din <= 0;
            ref_head <= 0;
            ref_tail <= 0;
        end else if (mem_ready) begin
            // Write logic
            push <= 1;
            din <= $urandom();
        end
    end
    @(negedge clk);
    for (int addr = 0; addr < DEPTH; addr++) begin
        push = 1;
        pop = 0;
        rand_data = $urandom();
        din = rand_data;
        ref_mem[addr] = rand_data;
        written_mask[addr] = 1;
        ref_tail = addr;
        // Wait for mem_ready
        do @(negedge clk); while (!mem_ready);
        push = 0;
    end


endmodule