//`include "Util.sv"
//`include "ALU16C.vhd"

module RecursionModule #(
    complex factorR
) (
    input complex in,
    input complex resetVal = 32'b0,
    input logic rst, clk,
    output complex out
);
    complex prod, sum, prev;

    assign out = sum;

    always_comb begin : calc
        prod = prev * factorR;
        sum = prod + in;
    end

    always_ff @(posedge clk) begin : recurse
        if (!rst)
            prev = resetVal;
        else
            prev = sum;
    end

endmodule