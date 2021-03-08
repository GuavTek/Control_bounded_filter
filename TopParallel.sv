`include "Util.sv"
`include "RecursionModule.sv"
`include "LUT.vhd"

module Parallel_top #(
    parameter stages = 32,
    parameter width = 16,
    parameter N = 3
) (
    input logic [N-1:0] in,
    input logic rst, clk,
    output logic [width-1:0] out
);
    complex w1;
    LUT #(.re(0.1), .im(0.0)) l1 (.sel(in[0]), .Result(w1));
    RecursionModule #(.factorR(0.97)) r1 (.in(w1), .rst(1'b1), .clk(clk), .out(out));
endmodule