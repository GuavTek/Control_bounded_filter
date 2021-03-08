//`include "Util.sv"
//`include "RecursionModule.sv"
//`include "LUT.vhd"

module Parallel_top #(
    parameter stages = 32,
    parameter width = 32,
    parameter N = 3
) (
    input logic [N-1:0] in,
    input logic rst, clk,
    output logic [width-1:0] out
);
    complex w1;
    complex f1;
    f1.r = 0.1;
    f1.i = 0.0;

    LUT #(.factor(f1)) l1 (.sel(in[0]), .Result(w1));
    RecursionModule #(.factorR(f1)) r1 (.in(w1), .rst(1'b1), .clk(clk), .out(out));
endmodule