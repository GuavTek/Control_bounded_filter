`ifndef INPUTREG_SV_
`define INPUTREG_SV_

// Collects a set of samples to one big sample
module InputReg #(
    parameter   DSR = 1,
                M = 4
) (
    input logic clk,
    input logic[$clog2(DSR)-1:0] pos,
    input logic[M-1:0] in,
    output logic[DSR*M-1:0] out
);
    logic[$clog2(M*DSR)-1:0] inSel;
    generate
        if (DSR > 1) begin
            always @(posedge clk) begin
                inSel = M*(DSR - pos)-1;
                out[inSel -: M] <= in;
            end
        end else begin
            assign out = in;
        end
    endgenerate 
endmodule

`endif