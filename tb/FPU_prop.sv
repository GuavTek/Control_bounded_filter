`ifndef FPU_PROP_SV_
`define FPU_PROP_SV_

`include "../sv/Util.sv"
`include "../sv/FPU.sv"

module FPU_prop #(parameter FPU_opcode op = ADD) (
    input floatType A, B,
    input logic clk,
    input floatType result
    );

    property Adder;
        @(posedge clk) 1 |-> (ftor(result) == (ftor(A) + ftor(B)));
    endproperty

    property Multiplier;
        @(posedge clk) 1 |-> (ftor(result) == (ftor(A) * ftor(B)));
    endproperty

    // Verify correct module behaviour
    if (op == ADD) begin
        assert property (Adder)
        else $display("Wrong FPU result! %f + %f != %f", ftor(A), ftor(B), ftor(result)); 
    end else begin
        assert property (Multiplier)
        else $display("Wrong FPU result! %f * %f != %f", ftor(A), ftor(B), ftor(result)); 
    end

endmodule

`endif // FPU_PROP_SV_
