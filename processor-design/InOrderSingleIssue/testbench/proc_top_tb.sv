module proc_top_tb;

logic clk;
logic resetn;

initial begin
    clk = 0;
    resetn = 1;

    // Load predefined RISC-V instructions into the array
    // Swap A = 25 and B = 75
    proc_top_inst.if_stage_inst.imem.mem_array[0]   = 32'h01908093; // ADDI x1, x1, 25
    proc_top_inst.if_stage_inst.imem.mem_array[1]   = 32'h04b10113; // ADDI x2, x2, 75
    proc_top_inst.if_stage_inst.imem.mem_array[2]   = 32'h002080b3; // ADD x1, x1, x2
    proc_top_inst.if_stage_inst.imem.mem_array[3]   = 32'h40208133; // SUB x2, x1, x2
    proc_top_inst.if_stage_inst.imem.mem_array[4]   = 32'h402080b3; // SUB x1, x1, x2
    proc_top_inst.if_stage_inst.imem.mem_array[5]   = 32'hffd08093; // ADDI x1, x1, -3
    proc_top_inst.if_stage_inst.imem.mem_array[6]   = 32'h0020a023; // SW x2, 0(x1)
    proc_top_inst.if_stage_inst.imem.mem_array[7]   = 32'h0000a183; // LW x3, 0(x1)
    proc_top_inst.if_stage_inst.imem.mem_array[8]   = 32'h0c310463; // BEQ x2, x3, 200
    proc_top_inst.if_stage_inst.imem.mem_array[58]  = 32'h01908093; // ADDI x1, x1, 25


    #0 resetn = 0; // Assert reset
    #20 resetn = 1; // Deassert reset
    #195;
    $finish; // End simulation after 1000 time units
end

always #5 clk = ~clk; // Generate clock signal

proc_top proc_top_inst (
    .clk(clk), // Connect the clock signal
    .resetn(resetn) // Connect the reset signal
);

endmodule