`ifndef VALIDCOUNT_SV_
`define VALIDCOUNT_SV_

// Counts for TopVal clock pulses, then stops
module ValidCount #(
    parameter   TopVal = 1,
                SecondVal = 0
) (
    input logic clk, rst,
    output logic out, out2
);

    logic[$clog2(TopVal):0] cnt;
    logic validClk;
    always @(posedge validClk, negedge rst) begin
        if(!rst) begin
            cnt <= 'b0;
            out2 <= 0;
        end else begin
            cnt <= cnt + 1;
            out2 <= (out2 | (cnt == SecondVal));
        end
    end

    assign out = cnt == TopVal;
    assign validClk = clk || out;
endmodule

`endif