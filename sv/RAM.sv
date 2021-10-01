`ifndef RAM_SV_
`define RAM_SV_

module RAM_single_bi #(
	parameter 	depth = 32,
	d_width = 3
	) (
	addr,
	clk, 
	write, 
	data
);
	input logic[$clog2(depth)-1:0]  addr;
	input logic clk, write;
	inout logic[d_width-1:0] data;
	`ifdef INCLUDE_RAM
	logic[d_width-1:0] mem[depth-1:0] = '{depth{0}};
	assign data = write ? 'bz : mem[addr];

	always @(posedge clk) begin
        if (write)
            mem[addr] = data;
   	end
	`endif
endmodule

// Unidirectional RAM with one read port
module RAM_single #(
	parameter 	depth = 32,
	d_width = 3
	) (
	addrIn, addrOut,
	clk, 
	write, 
	dataIn, dataOut
);
	input logic[$clog2(depth)-1:0]  addrIn, addrOut;
	input logic clk, write;
	input logic[d_width-1:0] dataIn;
	output logic[d_width-1:0] dataOut;
	`ifdef INCLUDE_RAM
	logic[d_width-1:0] mem[depth-1:0] = '{depth{0}};
	assign dataOut = mem[addrOut];

	always @(posedge clk) begin
        if (write)
            mem[addrIn] = dataIn;
   	end
	`endif
endmodule

// Unidirectional RAM with three read ports
module RAM_triple #(
	parameter 	depth = 32,
	d_width = 3
	) (
	addrIn, addrOut1, addrOut2, addrOut3,
	clk, 
	write, 
	dataIn, dataOut1, dataOut2, dataOut3
);
	input logic[$clog2(depth)-1:0]  addrIn, addrOut1, addrOut2, addrOut3;
	input logic clk, write;
	input logic[d_width-1:0] dataIn;
	output logic[d_width-1:0] dataOut1, dataOut2, dataOut3;
	`ifdef INCLUDE_RAM
	logic[d_width-1:0] mem[depth-1:0] = '{depth{0}};
	assign dataOut1 = mem[addrOut1];
	assign dataOut2 = mem[addrOut2];
	assign dataOut3 = mem[addrOut3];

	always @(posedge clk) begin
        if (write)
            mem[addrIn] = dataIn;
   	end
	`endif
endmodule

module RAM_dual_bi #(
	parameter 	depth = 32,
  	d_width=3
	) (
  	addr1, 
	addr2,
  	write1,
  	clk,
  	data1, 
	data2
);
	input logic[$clog2(depth)-1:0] addr1, addr2;
  	input logic write1;
  	input logic clk;
  	inout logic[d_width-1:0] data1;
	output logic[d_width-1:0] data2;
`ifdef INCLUDE_RAM
	logic[d_width-1:0] mem [depth-1:0] = '{depth{0}};
    assign data1 = write1 ? 'bz : mem[addr1];
	assign data2 = mem[addr2]; //write1 ? 'bz : mem[addr2];

	always @(posedge clk) begin
    	if (write1) 
			mem[addr1] = data1;
  	end   
`endif
endmodule
`endif