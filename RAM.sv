module RAM_single #(
	parameter 	depth = 32,
	d_width = 3
	) (
	input logic[$clog2(depth)-1:0]  addr,
	input logic clk, write, 
	inout logic[width-1:0] data
);
	logic[d_width-1:0] mem[depth-1:0];
	always @(posedge clk) begin
        if (write)
            mem[addr] <= data;
        else
			data <= mem[addr];
   	end
endmodule

module RAM_dual #(
	parameter 	depth = 32,
  	d_width=3
	) (
  	input logic[$clog2(depth)-1:0] addr1, addr2,
  	input logic write1,
  	input logic clk,
  	inout logic[d_width-1:0] data1, data2
);
    
	logic[d_width-1:0] mem [depth-1:0];
    
	always @(posedge clk) begin
    	if (write1) 
			mem[addr1] <= data1;
		else
			data1 <= mem[addr1];

		data2 <= mem[addr2];
  	end
        
endmodule