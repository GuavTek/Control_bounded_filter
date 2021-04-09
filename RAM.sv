module RAM_single #(parameter 	depth = 32,
								d_width = 3,
								a_width = 5) (
								input int addr,
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