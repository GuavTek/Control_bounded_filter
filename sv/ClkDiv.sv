`ifndef CLKDIV_SV_
`define CLKDIV_SV_

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
    logic clkO;
    generate
        if(DSR > 1) begin
            always @(posedge clkIn or negedge rst) begin
                if ((!rst) || (cnt == (DSR-1)))
                    cnt = 'b0;
                else
                    cnt++;

                if (cnt == 0)
                    clkO = 1;
                if (cnt == DSR/2)
                    clkO = 0;
                
            end
            assign cntOut = cnt;
            assign clkOut = clkO;
        end else begin
            assign clkOut = clkIn;
            assign cntOut = 'b0;
        end
    endgenerate 
endmodule

`endif