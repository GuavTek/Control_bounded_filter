`include "CFPU.sv"
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

    CFPU c1 (.A(prev), .B(factor), .op(MULT), .result(prod));
    CFPU c2 (.A(prod), .B(in), .op(ADD), .result(sum));

    always_ff @(posedge clk) begin : recurse
        if (!rst)
            prev = resetVal;
        else
            prev = sum;
    end

endmodule