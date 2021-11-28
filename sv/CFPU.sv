`ifndef CFPU_SV_
`define CFPU_SV_

`include "Util.sv"

module CFPU #(
    parameter   FPU_p::opcode op = FPU_p::ADD, 
    parameter   n_exp = 8, n_mant = 23,
    type float_t = struct {logic sign; logic[n_exp-1:0] exp; logic[n_mant-1:0] mant;},
    type complex_t = struct {float_t r; float_t i;}
    ) (
    input complex_t A, B,
    input logic clk,
    output complex_t result
);

generate
    case (op)
        FPU_p::ADD:
        begin
            FPU #(.op(FPU_p::ADD), .float_t(float_t), .n_exp(n_exp), .n_mant(n_mant)) fr1 (.A(A.r), .B(B.r), .clk(clk), .result(result.r));
            FPU #(.op(FPU_p::ADD), .float_t(float_t), .n_exp(n_exp), .n_mant(n_mant)) fi1 (.A(A.i), .B(B.i), .clk(clk), .result(result.i));
        end
        FPU_p::MULT:
        begin
            //cmulcc.r = (a.r * b.r) - (a.i * b.i);
            //cmulcc.i = (a.i * b.r) + (a.r * b.i);
            complex_t i1, i2;
            float_t temp2;
            // Real result
            FPU #(.op(FPU_p::MULT), .float_t(float_t), .n_exp(n_exp), .n_mant(n_mant)) fr1 (.A(A.r), .B(B.r), .clk(clk), .result(i1.r));
            FPU #(.op(FPU_p::MULT), .float_t(float_t), .n_exp(n_exp), .n_mant(n_mant)) fr2 (.A(A.i), .B(B.i), .clk(clk), .result(temp2));
            assign i2.r.sign = !temp2.sign;
            assign i2.r.exp = temp2.exp;
            assign i2.r.mant = temp2.mant;
            FPU #(.op(FPU_p::ADD), .float_t(float_t), .n_exp(n_exp), .n_mant(n_mant)) fr3 (.A(i1.r), .B(i2.r), .clk(clk), .result(result.r));

            // Imaginary result
            FPU #(.op(FPU_p::MULT), .float_t(float_t), .n_exp(n_exp), .n_mant(n_mant)) fi1 (.A(A.i), .B(B.r), .clk(clk), .result(i1.i));
            FPU #(.op(FPU_p::MULT), .float_t(float_t), .n_exp(n_exp), .n_mant(n_mant)) fi2 (.A(A.r), .B(B.i), .clk(clk), .result(i2.i));
            FPU #(.op(FPU_p::ADD), .float_t(float_t), .n_exp(n_exp), .n_mant(n_mant)) fi3 (.A(i1.i), .B(i2.i), .clk(clk), .result(result.i));
        end
    endcase
endgenerate
endmodule

`endif