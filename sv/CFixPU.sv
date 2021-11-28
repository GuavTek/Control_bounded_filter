`ifndef CFixPU_SV_
`define CFixPU_SV_

`include "Util.sv"
`include "FixPU.sv"

module CFixPU #(
    parameter   FPU_p::opcode op = FPU_p::ADD,
    parameter   n_int = 8,
                n_mant = 23
    ) (
    AR, AI, BR, BI, clk, resultR, resultI
);

localparam n_tot = n_int + n_mant;
input logic signed[n_tot:0] AR, AI, BR, BI;
input logic clk;
output logic signed[n_tot:0] resultR, resultI;

generate
    case (op)
        FPU_p::ADD:
        begin
            FixPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) fr1 (.A(AR), .B(BR), .clk(clk), .result(resultR));
            FixPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) fi1 (.A(AI), .B(BI), .clk(clk), .result(resultI));
        end
        FPU_p::MULT:
        begin
            //cmulcc.r = (a.r * b.r) - (a.i * b.i);
            //cmulcc.i = (a.i * b.r) + (a.r * b.i);
            logic signed[n_tot:0] tempRR, tempRI, tempRI_n, tempIR, tempII;
            logic signed[n_tot:0] temp2;
            // Real result
            FixPU #(.op(FPU_p::MULT), .n_int(n_int), .n_mant(n_mant)) fr1 (.A(AR), .B(BR), .clk(clk), .result(tempRR));
            FixPU #(.op(FPU_p::MULT), .n_int(n_int), .n_mant(n_mant)) fr2 (.A(AI), .B(BI), .clk(clk), .result(tempRI_n));
            assign tempRI = -tempRI_n;
            FixPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) fr3 (.A(tempRR), .B(tempRI), .clk(clk), .result(resultR));

            // Imaginary result
            FixPU #(.op(FPU_p::MULT), .n_int(n_int), .n_mant(n_mant)) fi1 (.A(AI), .B(BR), .clk(clk), .result(tempIR));
            FixPU #(.op(FPU_p::MULT), .n_int(n_int), .n_mant(n_mant)) fi2 (.A(AR), .B(BI), .clk(clk), .result(tempII));
            FixPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) fi3 (.A(tempIR), .B(tempII), .clk(clk), .result(resultI));
        end
    endcase
endgenerate
endmodule

`endif