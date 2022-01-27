`ifndef FPU_SV_
`define FPU_SV_

`include "Util.sv"

module FPU #(
    parameter   FPU_p::opcode op = FPU_p::ADD,
    parameter   n_exp = 8, n_mant = 23,
    parameter   type float_t = struct {logic sign; logic[7:0] exp; logic[22:0] mant;}
    ) (
    A, B, clk, result
);
    input float_t A, B;
    input logic clk;
    output float_t result;
    localparam n_tot = n_exp + n_mant;

    logic[n_tot + 1:0] s1, s2, r1;

    fNToRecFN #(.expWidth(n_exp), .sigWidth(n_mant+1)) aConv (.in(A), .out(s1));
    fNToRecFN #(.expWidth(n_exp), .sigWidth(n_mant+1)) bConv (.in(B), .out(s2));
    recFNToFN #(.expWidth(n_exp), .sigWidth(n_mant+1)) resConv (.in(r1), .out(result));

    generate
        case (op)
        FPU_p::ADD:
        begin
            logic[4:0] dummy;
            addRecFN #(.expWidth(n_exp), .sigWidth(n_mant+1)) add1 (.control(`flControl_tininessAfterRounding), .subOp(1'b0), .a(s1), .b(s2), .roundingMode(`round_near_even), .out(r1), .exceptionFlags(dummy));
        end
        FPU_p::MULT:
        begin 
            logic[4:0] dummy;
            mulRecFN #(.expWidth(n_exp), .sigWidth(n_mant+1)) mul1 (.control(`flControl_tininessAfterRounding), .a(s1), .b(s2), .roundingMode(`round_near_even), .out(r1), .exceptionFlags(dummy));
        end
        endcase
    endgenerate

endmodule

`endif