`ifndef RECURSIONMODULE_SV_
`define RECURSIONMODULE_SV_

`include "Util.sv"

module RecursionModule #(
    parameter   factorR = 0.0,
                factorI = 0.0
) (
    input complex in,
    input complex resetVal,
    input logic rst, clk,
    output complex out
);
    complex prod, sum, prev, factor;
    assign factor.r = factorR;
    assign factor.i = factorI;
    assign out = sum;

    CFPU #(.op(MULT)) c1 (.A(prev), .B(factor), .result(prod));
    CFPU #(.op(ADD)) c2 (.A(prod), .B(in), .result(sum));

    always_ff @(posedge clk) begin : recurse
        if (!rst)
            prev = resetVal;
        else
            prev = sum;
    end

endmodule
`endif
