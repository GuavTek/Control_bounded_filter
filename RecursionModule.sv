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
    ALU16C a1 (.A(in), .B(prod), .R(sum), .func(ALU_ADD));
    ALU16C a2 (.A(factorR), .B(prev), .R(prod), .func(ALU_MULT));

    assign out = sum;

    always_ff @(posedge clk) begin : recurse
        if (!rst)
            prev = resetVal;
        else
            prev = sum;
    end

endmodule