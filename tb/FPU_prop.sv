`ifndef FPU_PROP_SV_
`define FPU_PROP_SV_

`include "Util_TB.sv"
`include "../sv/FPU.sv"

// How much results can vary due to precision differences
`define F_SLACK 0.01

module FPU_prop #(
    parameter   FPU_p::opcode op = FPU_p::ADD, 
    parameter   n_exp = 8, n_mant = 22,
                type float_t = struct packed {logic sign; logic[7:0] exp; logic[22:0] mant;}
    ) (
    input float_t A, B,
    input logic clk,
    input float_t result
    );

    property Adder;
        @(negedge clk) absr(convert_nonsynth #(.f_exp(n_exp), .f_mant(n_mant))::ftor(result) - (convert_nonsynth #(.f_exp(n_exp), .f_mant(n_mant))::ftor(A) + convert_nonsynth #(.f_exp(n_exp), .f_mant(n_mant))::ftor(B))) <= (`F_SLACK*absr(convert_nonsynth #(.f_exp(n_exp), .f_mant(n_mant))::ftor(result) + 0.0000001));
    endproperty

    property Multiplier;
        @(negedge clk) absr(convert_nonsynth #(.f_exp(n_exp), .f_mant(n_mant))::ftor(result) - (convert_nonsynth #(.f_exp(n_exp), .f_mant(n_mant))::ftor(A) * convert_nonsynth #(.f_exp(n_exp), .f_mant(n_mant))::ftor(B))) <= (`F_SLACK*absr(convert_nonsynth #(.f_exp(n_exp), .f_mant(n_mant))::ftor(result) + 0.0000001));
    endproperty

    // Verify correct module behaviour
    if (op == FPU_p::ADD) begin
        assert property (disable iff($isunknown(A) || $isunknown(B)) Adder)
        else $display("Wrong FPU result! %f + %f != %f, expecting %f", convert_nonsynth #(.f_exp(n_exp), .f_mant(n_mant))::ftor(A), convert_nonsynth #(.f_exp(n_exp), .f_mant(n_mant))::ftor(B), convert_nonsynth #(.f_exp(n_exp), .f_mant(n_mant))::ftor(result), convert_nonsynth #(.f_exp(n_exp), .f_mant(n_mant))::ftor(A) + convert_nonsynth #(.f_exp(n_exp), .f_mant(n_mant))::ftor(B)); 
    end else begin
        assert property (disable iff($isunknown(A) || $isunknown(B)) Multiplier)
        else $display("Wrong FPU result! %f * %f != %f, expecting %f", convert_nonsynth #(.f_exp(n_exp), .f_mant(n_mant))::ftor(A), convert_nonsynth #(.f_exp(n_exp), .f_mant(n_mant))::ftor(B), convert_nonsynth #(.f_exp(n_exp), .f_mant(n_mant))::ftor(result), convert_nonsynth #(.f_exp(n_exp), .f_mant(n_mant))::ftor(A) * convert_nonsynth #(.f_exp(n_exp), .f_mant(n_mant))::ftor(B)); 
    end

endmodule

`endif // FPU_PROP_SV_
