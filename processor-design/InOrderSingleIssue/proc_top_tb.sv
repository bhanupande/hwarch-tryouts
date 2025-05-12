module proc_top_tb;

logic clk;
logic resetn;

initial begin
    clk = 0;
    resetn = 1;

    // Load predefined RISC-V instructions into the array
    proc_top_inst.if_stage_inst.imem.mem_array[0]   = 32'h3ff08093; // ADDI x1, x1, 1023 (R-type)
    proc_top_inst.if_stage_inst.imem.mem_array[1]   = 32'h00110193; // ADDI x3, x2, 1 (R-type)
    proc_top_inst.if_stage_inst.imem.mem_array[2]   = 32'h00000013; // NOP (No operation)
    proc_top_inst.if_stage_inst.imem.mem_array[3]   = 32'h00000013; // NOP (No operation)
    proc_top_inst.if_stage_inst.imem.mem_array[4]   = 32'h001081b3; // ADD x3, x1, x1
    proc_top_inst.if_stage_inst.imem.mem_array[5]   = 32'h01420213; // addi x4, x4, 20
    proc_top_inst.if_stage_inst.imem.mem_array[6]   = 32'h00000013; // NOP (No operation)
    proc_top_inst.if_stage_inst.imem.mem_array[7]   = 32'h00000013; // NOP (No operation)
    proc_top_inst.if_stage_inst.imem.mem_array[8]   = 32'h00000013; // NOP (No operation)
    proc_top_inst.if_stage_inst.imem.mem_array[9]   = 32'h00322023; // sw x3, 0(x4)
    proc_top_inst.if_stage_inst.imem.mem_array[10]   = 32'h00022283; // lw x5, 0(x4)
    proc_top_inst.if_stage_inst.imem.mem_array[11]   = 32'h00000013; // NOP (No operation)
    proc_top_inst.if_stage_inst.imem.mem_array[12]  = 32'h00000013; // NOP (No operation)
    proc_top_inst.if_stage_inst.imem.mem_array[13]  = 32'h00000013; // NOP (No operation)
    proc_top_inst.if_stage_inst.imem.mem_array[14]  = 32'h00228293; // addi x5, x5, 2
    proc_top_inst.if_stage_inst.imem.mem_array[15]  = 32'h00000013; // NOP (No operation)
    proc_top_inst.if_stage_inst.imem.mem_array[16]  = 32'h00000013; // NOP (No operation)
    proc_top_inst.if_stage_inst.imem.mem_array[17]  = 32'h00000013; // NOP (No operation)
    proc_top_inst.if_stage_inst.imem.mem_array[18]  = 32'h02328333; // mul x6, x5, x3
    proc_top_inst.if_stage_inst.imem.mem_array[19]  = 32'h00000013; // NOP (No operation)

    #0 resetn = 0; // Assert reset
    #20 resetn = 1; // Deassert reset
    #300;
    $finish; // End simulation after 1000 time units
end

always #5 clk = ~clk; // Generate clock signal

proc_top proc_top_inst (
    .clk(clk), // Connect the clock signal
    .resetn(resetn) // Connect the reset signal
);

endmodule