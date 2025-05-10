module iosi_top (
    input logic clk,            // Clock signal
    input logic resetn,        // Active low reset signal
    input logic [31:0] opcode, // Instruction packet from decode stage
    input logic [31:0] pc_in, // Program counter input
    output logic [31:0] pc_out // Program counter output
);

rv32_instr_packet_t instruction_packet; // Instruction packet for the decode stage
rv32_issue_packet_t issue_packet; // Issue packet for the regfile stage
rv32_writeback_packet_t writeback_packet; // Writeback packet for the regfile stage

logic [4:0] reg_write_addr; // Destination register value
logic reg_write_enable; // Register write enable signal
logic mem_read_enable; // Memory read enable signal
logic mem_write_enable; // Memory write enable signal
logic [2:0] load_sel; // Load select signal for memory operations
logic [1:0] store_sel; // Store select signal for memory operations
logic branch_taken; // Branch taken signal
logic [31:0] branch_target; // Branch target address
logic [2:0] branch_type; // Branch type signal
logic [31:0] mem_addr; // Memory address for load/store operations
logic [31:0] mem_data; // Data to write to memory
logic [31:0] reg_write_data; // Data to write back to register file



decode decode_inst (
    .instruction(opcode), // Connect the instruction input
    .instruction_packet(instruction_packet) // Connect the output packet
);

regfile regfile_inst (
    .clk(clk), // Connect the clock signal
    .resetn(resetn), // Connect the reset signal
    .instruction_packet(instruction_packet), // Connect the instruction packet
    .writeback_packet(writeback_packet), // Connect the writeback packet
    .issue_packet(issue_packet) // Connect the output packet for the next stage
);

execute execute_inst (
    .clk(clk), // Connect the clock signal
    .resetn(resetn), // Connect the reset signal
    .pc_in(pc_in), // Connect the program counter input
    .issue_packet(issue_packet), // Connect the issue packet
    .reg_write_addr(reg_write_addr), // Connect the register write address
    .reg_write_enable(reg_write_enable), // Connect the register write enable signal
    .mem_read_enable(mem_read_enable), // Connect the memory read enable signal
    .mem_write_enable(mem_write_enable), // Connect the memory write enable signal
    .load_sel(load_sel), // Connect the load select signal
    .store_sel(store_sel), // Connect the store select signal
    .branch_taken(branch_taken), // Connect the branch taken signal
    .branch_target(branch_target), // Connect the branch target address
    .branch_type(branch_type), // Connect the branch type signal
    .mem_addr(mem_addr), // Connect the memory address
    .mem_data(mem_data), // Connect the data to write to memory
    .reg_write_data(reg_write_data), // Connect the data to write back to register file
    .pc_out(pc_out) // Connect the program counter output
);

memstage memstage_inst (
    .clk(clk), // Connect the clock signal
    .resetn(resetn), // Connect the reset signal
    .reg_write_enable(reg_write_enable), // Connect the register write enable signal
    .mem_read_enable(mem_read_enable), // Connect the memory read enable signal
    .mem_write_enable(mem_write_enable), // Connect the memory write enable signal
    .load_sel(load_sel), // Connect the load select signal
    .store_sel(store_sel), // Connect the store select signal
    .branch_taken(branch_taken), // Connect the branch taken signal
    .branch_target(branch_target), // Connect the branch target address
    .branch_type(branch_type), // Connect the branch type signal
    .mem_addr_from_ex(mem_addr), // Connect the memory address for load/store operations
    .mem_data_from_ex(mem_data), // Connect the data from EX stage for store operations
    .reg_write_addr(reg_write_addr), // Connect the register address to write back
    .reg_write_data(reg_write_data), // Connect the data to write back to register file
    .pc_from_ex(pc_out), // Connect the program counter output
    .mem_ready(1'b1), // Connect the memory ready signal
    .mem_data_in(mem_data_in), // Connect the data read from memory
    .mem_data_out(mem_data_out), // Connect the data read from memory
    .mem_write_enable_out(mem_write_enable_out), // Connect the memory write enable signal
    .mem_read_enable_out(mem_read_enable_out), // Connect the memory read enable signal
    .mem_addr_out(mem_addr_out), // Connect the memory address for load/store operations
    .reg_write_data_out(reg_write_data_out), // Connect the data to write back to register file
    .reg_write_enable_out(reg_write_enable_out), // Connect the register write enable signal
    .reg_write_addr_out(reg_write_addr_out), // Connect the register address to write back
    .pc_next(pc_out) // Connect the next program counter value
);

mem dmem_inst (
    .clk(clk), // Connect the clock signal
    .rstn(resetn), // Connect the reset signal
    .mem_addr(mem_addr_out), // Connect the memory address for load/store operations
    .mem_data_in(mem_data_out), // Connect the data to write to memory
    .mem_write_enable(mem_write_enable_out), // Connect the memory write enable signal
    .mem_read_enable(mem_read_enable_out), // Connect the memory read enable signal
    .mem_data_out(mem_data_in) // Connect the data read from memory
);
endmodule