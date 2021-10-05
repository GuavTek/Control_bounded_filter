`ifndef RAM_PROP_SV_
`define RAM_PROP_SV_

`include "../sv/RAM.sv"

module RAM_single_prop #(
	parameter 	depth = 32,
	d_width = 3
	) (
	addrIn, addrOut,
	clk, rst, 
	write, 
	dataIn, dataOut,
	mem
	);
	input logic[$clog2(depth)-1:0]  addrIn, addrOut;
	input logic clk, write, rst;
	input logic[d_width-1:0] dataIn;
	input logic[d_width-1:0] dataOut;
	input logic[d_width-1:0] mem[depth-1:0];

	assert property (@(posedge clk) write |-> mem[addrIn] == dataIn) 
	else   $warning("Written data was not stored properly!! \n%h was written, %h was stored in address %d", dataIn, mem[addrIn], addrIn);

	assert property (@(posedge clk) 1 |-> dataOut == mem[addrOut])
	else $warning("Data out from port is not equal memory!! \n%h at port, %h at address %d", dataOut, mem[addrOut], addrOut);

    assert property (@(posedge clk) disable iff($isunknown(addrIn) || !rst) write |=> !$isunknown(mem[$past(addrIn)])) 
    else   $warning("Data in ram is unknown!! \n%h at address %d", dataIn, $past(addrIn));
endmodule

module RAM_triple_prop #(
	parameter 	depth = 32,
	d_width = 3
	) (
	addrIn, addrOut1, addrOut2, addrOut3,
	clk, rst,
	write, 
	dataIn, dataOut1, dataOut2, dataOut3,
	mem
	);
	input logic[$clog2(depth)-1:0]  addrIn, addrOut1, addrOut2, addrOut3;
	input logic clk, write, rst;
	input logic[d_width-1:0] dataIn;
	input logic[d_width-1:0] dataOut1, dataOut2, dataOut3;
	input logic[d_width-1:0] mem[depth-1:0];

	assert property (@(posedge clk) write |-> mem[addrIn] == dataIn) 
	else   $warning("Written data was not stored properly!! \n%h was written, %h was stored in address %d", dataIn, mem[addrIn], addrIn);

	assert property (@(posedge clk) 1 |-> dataOut1 == mem[addrOut1])
	else $warning("Data out 1 from port is not equal memory!! \n%h at port, %h at address %d", dataOut1, mem[addrOut1], addrOut1);

	assert property (@(posedge clk) 1 |-> dataOut2 == mem[addrOut2])
	else $warning("Data out 2 from port is not equal memory!! \n%h at port, %h at address %d", dataOut2, mem[addrOut2], addrOut2);

	assert property (@(posedge clk) 1 |-> dataOut3 == mem[addrOut3])
	else $warning("Data out 3 from port is not equal memory!! \n%h at port, %h at address %d", dataOut3, mem[addrOut3], addrOut3);

    assert property (@(posedge clk) disable iff($isunknown(addrIn) || !rst) write |=> !$isunknown(mem[$past(addrIn)])) 
    else   $warning("Data in ram is unknown!! \n%h at address %d", dataIn, $past(addrIn));
endmodule

module RAM_single_bi_prop #(
	parameter 	depth = 32,
	d_width = 3
	) (
	addr,
	clk, 
	write, 
	data,
    mem
	);
	input logic[$clog2(depth)-1:0]  addr;
	input logic clk, write;
	input logic[d_width-1:0] data;
    input logic[d_width-1:0] mem[depth-1:0];

	//assert property (@(posedge clk) write |-> mem[addr] == data) 
	//else   $warning("Written data was not stored properly!! \n%h was written, %h was stored in address %d", data, mem[addr], addr);

	assert property (@(posedge clk) !write |-> data == mem[addr])
	else $warning("Data in memory is not equal port!! \n%h at port, %h at address %d", data, mem[addr], addr);

    assert property (@(posedge clk) disable iff($isunknown(addr)) !write |-> !$isunknown(data)) 
    else   $warning("Data in ram is unknown!! \n%h at address %d", data, addr);

endmodule

module RAM_dual_bi_prop #(
	parameter 	depth = 32,
  	d_width = 3
	) (
  	addr1, 
	addr2,
  	write1,
  	clk,
  	data1, 
	data2,
    mem
	);
	input logic[$clog2(depth)-1:0] addr1, addr2;
  	input logic write1;
  	input logic clk;
  	input logic[d_width-1:0] data1, data2;
	input logic[d_width-1:0] mem [depth-1:0];

	//assert property (@(posedge clk) write1 |-> mem[addr1] == data1) 
	//else   $warning("Written data was not stored properly!! \n%h was written, %h was stored in address %d", data1, mem[addr1], addr1);

	assert property (@(posedge clk) !write1 |-> data1 == mem[addr1])
	else $warning("Data1 in memory is not equal port!! \n%h at port, %h at address %d", data1, mem[addr1], addr1);

	assert property (@(posedge clk) !write1 |-> data2 == mem[addr2])
	else $warning("Data2 in memory is not equal port!! \n%h at port, %h at address %d", data2, mem[addr2], addr2);

	assert property (@(posedge clk) disable iff($isunknown(addr1)) !write1 |-> !$isunknown(data1)) 
    else   $warning("Data1 in ram is unknown!! \n%h at address %d", data1, addr1);

    assert property (@(posedge clk) disable iff($isunknown(addr2)) !write1 |-> !$isunknown(data2)) 
    else   $warning("Data2 in ram is unknown!! \n%h at address %d", data2, addr2);

endmodule
`endif