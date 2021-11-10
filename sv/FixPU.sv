`ifndef FIXPU_SV_
`define FIXPU_SV_

`include "Util.sv"

module FixPU #(
    parameter   FPU_opcode op = ADD,
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
        ADD:
        begin
            assign result = A + B;
        end
        MULT:
        begin 
            logic signed[2*n_tot:0] AB;
            assign AB = A * B;
            assign result = AB >>> n_mant;
        end
        endcase
    endgenerate

endmodule

`endif