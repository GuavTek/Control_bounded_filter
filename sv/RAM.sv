module RAM_single #(
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
	logic[d_width-1:0] dout;
	logic[d_width-1:0] mem[depth-1:0];
	assign data = dout;

	always @(posedge clk) begin
        if (write)
            mem[addr] = dout;
        else
			dout = mem[addr];
   	end
`endif
endmodule

module RAM_dual #(
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
  	inout logic[d_width-1:0] data1, data2;
`ifdef INCLUDE_RAM
    logic[d_width-1:0] dout1, dout2;
	logic[d_width-1:0] mem [depth-1:0];
    assign data1 = dout1;
	assign data2 = dout2;

	always @(posedge clk) begin
    	if (write1) 
			mem[addr1] = dout1;
		else
			dout1 = mem[addr1];

		dout2 = mem[addr2];
  	end   
`endif
endmodule