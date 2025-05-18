module load_store_queue #(
    parameter int QueueDepth = 16, // Number of entries in the queue
    parameter int AddressWidth = 32 // Width of each entry (in bits)
)(
    input logic clk, // Clock signal
    input logic rstn, // Active-low reset signal
    input logic [AddressWidth-1:0] load_addr, // Load address
    input logic push, // Push signal (write enable)
    input logic pop, // Pop signal (read enable)
    output logic [AddressWidth-1:0] data_out, // Data output
    output logic full, // Full flag
    output logic empty // Empty flag
);


endmodule