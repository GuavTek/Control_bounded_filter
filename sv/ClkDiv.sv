`ifndef CLKDIV_SV_
`define CLKDIV_SV_

module ClkDiv #(
    parameter DSR = 1
) (
    input wire clkIn, rst,
    output wire clkOut,
    output wire [$clog2(DSR)-1:0] cntOut
);
    logic[$clog2(DSR)-1:0] cnt;      // Prescale counter
    logic prevRst, clkO;
    generate
        if(DSR > 1) begin
            always @(posedge clkIn) begin
                if (!rst && prevRst)
                    cnt = 0;
                else if (cnt == (DSR-1)) begin
                    cnt = 0;
                    clkO = 1;
                end else
                    cnt++;
                prevRst = rst;

                if (cnt == DSR/2)
                    clkO = 0;
                
            end
            assign cntOut = cnt;
            assign clkOut = clkO;
        end else begin
            assign clkOut = clkIn;
        end
    endgenerate 
endmodule

`endif