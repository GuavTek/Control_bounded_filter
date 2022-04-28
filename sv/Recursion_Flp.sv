`ifndef RECURSION_FLP_SV_
`define RECURSION_FLP_SV_

`include "CFPU.sv"
`include "Util.sv"

module Recursion_Flp #(
    parameter logic signed[63:0] factorR = 0,
                        factorI = 0,
    parameter           n_int = 15,
                        n_mant = 48,
                        f_exp = 8,
                        f_mant = 23,
    type float_t = struct {logic sign; logic[f_exp-1:0] exp; logic[f_mant-1:0] mant;},
    type complex_t = struct {float_t r; float_t i;}
) (
    input complex_t in,
    input complex_t loadVal,
    input logic rst, clk, load,
    output complex_t out
);
    complex_t prod, sum, prev, factor;

    // Convert loopfactor
    ConvertITOF #(.n_int(n_int), .n_mant(n_mant), .f_exp(f_exp), .f_mant(f_mant), .in(factorR)) itofR ();
    ConvertITOF #(.n_int(n_int), .n_mant(n_mant), .f_exp(f_exp), .f_mant(f_mant), .in(factorI)) itofI ();
    assign factor.r = itofR.result;
    assign factor.i = itofI.result;

    assign out = sum;

    CFPU #(.op(FPU_p::MULT), .n_exp(f_exp), .n_mant(f_mant), .float_t(float_t), .complex_t(complex_t)) c1 (.A(prev), .B(factor), .clk(clk), .result(prod));
    CFPU #(.op(FPU_p::ADD), .n_exp(f_exp), .n_mant(f_mant), .float_t(float_t), .complex_t(complex_t)) c2 (.A(prod), .B(in), .clk(clk), .result(sum));

    always @(posedge clk, negedge rst) begin : recurse
        if (!rst)
            prev <= {'b0, 'b0 };
        else if (!load)
            prev <= loadVal;
        else
            prev <= sum;
    end

endmodule

`endif
