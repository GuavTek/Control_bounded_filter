`ifndef FPU_PROP_SV_
`define FPU_PROP_SV_

`include "../sv/Util.sv"
`include "../sv/FPU.sv"

// How much results can vary due to precision differences
`define F_SLACK 0.01

module FPU_prop #(parameter FPU_opcode op = ADD) (
    input floatType A, B,
    input logic clk,
    input floatType result
    );

    property Adder;
        @(negedge clk) absr(ftor(result) - (ftor(A) + ftor(B))) <= (`F_SLACK*absr(ftor(result) + 0.0000001));
    endproperty

    property Multiplier;
        @(negedge clk) absr(ftor(result) - (ftor(A) * ftor(B))) <= (`F_SLACK*absr(ftor(result) + 0.0000001));
    endproperty

    // Verify correct module behaviour
    if (op == ADD) begin
        assert property (disable iff($isunknown(A) || $isunknown(B)) Adder)
        else $display("Wrong FPU result! %f + %f != %f, expecting %f", ftor(A), ftor(B), ftor(result), ftor(A) + ftor(B)); 
    end else begin
        assert property (disable iff($isunknown(A) || $isunknown(B)) Multiplier)
        else $display("Wrong FPU result! %f * %f != %f, expecting %f", ftor(A), ftor(B), ftor(result), ftor(A) * ftor(B)); 
    end

endmodule

`endif // FPU_PROP_SV_
