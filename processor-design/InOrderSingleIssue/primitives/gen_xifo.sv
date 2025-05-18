//------------------------------------------------------------------------------
// Project      : Generic FIFO/LIFO (Queue/Stack) Primitive
// File         : gen_xifo.sv
// Description  : Parameterized module implementing either a FIFO queue or LIFO
//                stack, selectable via the Mode parameter. Supports push/pop,
//                full/empty flags, and parameterizable data width and depth.
// Author       : Bhanu Pande
// Date         : 05/18/2025
//------------------------------------------------------------------------------
// Parameters:
//   QueueDepth : Number of entries in the queue/stack
//   DWidth     : Width of each entry (in bits)
//   Mode       : "FIFO" for queue, "LIFO" for stack
//------------------------------------------------------------------------------
// Interface:
//   clk        : Clock signal
//   rstn       : Active-low reset
//   data_in    : Data input
//   push       : Push (write) enable
//   pop        : Pop (read) enable
//   data_out   : Data output
//   full       : Full flag
//   empty      : Empty flag
//------------------------------------------------------------------------------

module gen_xifo #(
    parameter int QueueDepth = 16, // Number of entries in the queue
    parameter int DWidth = 32,     // Width of each entry (in bits)
    parameter Mode = "FIFO"        // FIFO or LIFO mode
)(
    input  logic                  clk,      // Clock signal
    input  logic                  rstn,     // Active-low reset signal
    input  logic [DWidth-1:0]     data_in,  // Data input
    input  logic                  push,     // Push signal (write enable)
    input  logic                  pop,      // Pop signal (read enable)
    output logic [DWidth-1:0]     data_out, // Data output
    output logic                  full,     // Full flag
    output logic                  empty     // Empty flag
);

generate
    //------------------------------------------------------------------------------
    // FIFO Implementation (Queue)
    //------------------------------------------------------------------------------
    if (Mode == "FIFO") begin
        // Internal memory and pointers
        logic [DWidth-1:0] fifo_mem [QueueDepth-1:0];
        logic [$clog2(QueueDepth)-1:0] head, tail;

        // Full when next head equals tail, empty when head equals tail
        assign full  = (head + 1) == tail;
        assign empty = head == tail;

        // Synchronous logic for head/tail pointers and memory
        always_ff @(posedge clk or negedge rstn) begin
            if (!rstn) begin
                head <= 0;
                tail <= 0;
            end else begin
                if (push && !full) begin
                    fifo_mem[head] <= data_in;
                    head <= (head + 1);
                end
                if (pop && !empty) begin
                    tail <= (tail + 1);
                end
            end
        end

        // Output data at the tail pointer
        always_comb begin
            data_out = fifo_mem[tail];
        end

    //------------------------------------------------------------------------------
    // LIFO Implementation (Stack)
    //------------------------------------------------------------------------------
    end else if (Mode == "LIFO") begin
        // Internal memory and top pointer
        logic [DWidth-1:0] stack_mem [QueueDepth-1:0];
        logic [$clog2(QueueDepth)-1:0] top;

        // Full when top+1 equals depth, empty when top is zero
        assign full  = (top + 1) == QueueDepth;
        assign empty = top == 0;

        // Synchronous logic for top pointer and memory
        always_ff @(posedge clk or negedge rstn) begin
            if (!rstn) begin
                top <= 0;
            end else begin
                if (push && !full) begin
                    stack_mem[top] <= data_in;
                    top <= (top + 1);
                end
                if (pop && !empty) begin
                    top <= (top - 1);
                end
            end
        end

        // Output data at the top-1 position (last pushed)
        always_comb begin
            data_out = top > 0 ? stack_mem[top-1] : stack_mem[0];
        end
    end
endgenerate

endmodule