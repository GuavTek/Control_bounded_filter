`ifndef RECURSIONMODULE_SV_
`define RECURSIONMODULE_SV_

`include "Util.sv"

module RecursionModule #(
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
    input complex_t resetVal,
    input logic rst, clk,
    output complex_t out
);
    complex_t prod, sum, prev, factor, prevSum;
    logic resetting;

    // Convert loopfactor
    ConvertITOF #(.n_int(n_int), .n_mant(n_mant), .f_exp(f_exp), .f_mant(f_mant), .in(factorR)) itofR ();
    ConvertITOF #(.n_int(n_int), .n_mant(n_mant), .f_exp(f_exp), .f_mant(f_mant), .in(factorI)) itofI ();
    assign factor.r = itofR.result;
    assign factor.i = itofI.result;
    assign out = prevSum;
    assign prev = resetting ? prevSum : resetVal;

    CFPU #(.op(FPU_p::MULT), .n_exp(f_exp), .n_mant(f_mant), .float_t(float_t), .complex_t(complex_t)) c1 (.A(prev), .B(factor), .clk(clk), .result(prod));
    CFPU #(.op(FPU_p::ADD), .n_exp(f_exp), .n_mant(f_mant), .float_t(float_t), .complex_t(complex_t)) c2 (.A(prod), .B(in), .clk(clk), .result(sum));

    always_ff @(posedge clk) begin : recurse
        resetting <= rst;
        prevSum <= sum;
    end

endmodule

`endif
