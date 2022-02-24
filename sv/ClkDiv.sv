`ifndef CLKDIV_SV_
`define CLKDIV_SV_

`include "Delay.sv"

// clkOut is DSR times slower than clkIn
// cntOut is the internal counter
// Has asynchronous reset
module ClkDiv #(
    parameter DSR = 1
) (
    input logic clkIn, rst,
    output logic clkOut,
    output logic [$clog2(DSR)-1:0] cntOut
);
    logic[$clog2(DSR)-1:0] cnt;      // Prescale counter
    generate
        if(DSR > 1) begin
            always @(posedge clkIn) begin
                if ((!rst) || (cnt == (DSR-1)))
                    cnt <= 'b0;
                else
                    cnt <= cnt + 1;

                if ((cnt == DSR/2) || !rst)
                    clkOut = 0;
                if (cnt == 0)
                    clkOut = 1;
                
            end
            assign cntOut = cnt;
        end else begin
            assign clkOut = clkIn;
            assign cntOut = 'b0;
        end
    endgenerate 
endmodule

`endif