`ifndef FIXPU_SV_
`define FIXPU_SV_

`include "Util.sv"

module FixPU #(
    parameter   FPU_p::opcode op = FPU_p::ADD,
    parameter   n_int = 8,
                n_mant = 23
    ) (
    A, B, clk, result
);
    localparam n_tot = n_int + n_mant;
    input logic signed[n_tot:0] A, B;
    input logic clk;
    output logic signed[n_tot:0] result;

    generate
        case (op)
        FPU_p::ADD:
        begin
            assign result = A + B;
        end
        FPU_p::MULT:
        begin 
            logic signed[2*n_tot:0] AB;
            assign AB = A * B;
            assign result = AB >>> n_mant;
        end
        endcase
    endgenerate

endmodule

`endif