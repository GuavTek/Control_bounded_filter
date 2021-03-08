
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
    factor.r = factorR;
    factor.i = factorI;

    assign out = sum;

    always_comb begin : calc
        prod = cmulcc(prev, factor);   // prod = prev * factorR;
        sum = caddcc(prod, in);         // sum = prod + in
    end

    always_ff @(posedge clk) begin : recurse
        if (!rst)
            prev = resetVal;
        else
            prev = sum;
    end

endmodule