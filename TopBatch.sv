`include "Util.sv"
`include "FPU.sv"
`include "CFPU.sv"
`include "RecursionModule.sv"
`include "LUT.sv"
`include "RAM.sv"

module Batch_top #(
    parameter stages = 32,
    parameter width = 32,
    parameter N = 3
) (
    input logic [N-1:0] in,
    input logic rst, clk,
    output logic [width-1:0] out
);
    complex w1, w2;

    assign out = w2.r;
    LUT #(.re(0.1)) l1 (.sel(in[0]), .result(w1));
    RecursionModule #(.factorR(0.2), .factorI(-0.2)) r1 (.in(w1), .rst(1'b1), .clk(clk), .out(w2));
endmodule