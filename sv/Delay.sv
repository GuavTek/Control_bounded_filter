`ifndef DELAY_SV_
`define DELAY_SV_

module Delay #(
    parameter size = 1, delay = 0
) (
    input logic[size-1:0] in, 
    input logic clk,
    output logic[size-1:0] out
);
    // Make sure we don't get negative variable sizes
    localparam tempDelay = (delay < 0) ? 0 : delay;
    generate
        if(delay > 0) begin
            logic[size-1:0] inDelay[tempDelay+1];
            for (genvar i = 1; i <= delay; i++) begin
                always @(posedge clk) begin
                    inDelay[i] <= inDelay[i-1];
                end
            end

            assign inDelay[0] = in;
            assign out = inDelay[delay];
        end else begin
            assign out = in;
        end
    endgenerate
endmodule
`endif
