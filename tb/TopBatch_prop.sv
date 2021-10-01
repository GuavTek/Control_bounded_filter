`ifndef TOPBATCH_PROP_SV_
`define TOPBATCH_PROP_SV_

`include "../sv/TopBatch.sv"

module Batch_top_prop #(
    parameter depth = 32,
    parameter N = 3,
    parameter OSR = 1
) (
    input wire [N-1:0] in,
    input logic rst, clk, clkDS,
    input floatType out,
    input logic[$clog2($rtoi($ceil(depth / OSR)))-1:0] dBatCount, dBatCountRev, 
    input logic cyclePulse, regProp,
    input logic[1:0] cycle, cycleLH, cycleIdle, cycleCalc,
    input logic[N*OSR-1:0] inShift,
    input logic[N*OSR-1:0] slh, scob, sf_delay, scof
);

task automatic lookahead_a();
    logic[N*OSR-1:0] inSample;
    int delay;
    if(rst) begin
        inSample = inShift;
        delay = dBatCount;
        repeat(2*(depth-delay)) @(posedge clk);
        if(slh != inSample)
            $error("Lookahead sample was misplaced!! %h was sent in, but %h came out", inSample, slh);
        else 
            return;
    end
endtask // lookahead_a

task automatic meanB_a();
    logic[N*OSR-1:0] inSample;
    int delay;
    if(rst) begin
        inSample = inShift;
        delay = dBatCount;
        repeat(4*depth-2*delay) @(posedge clk);
        if(scob != inSample)
            $error("Backward mean sample was misplaced!! %h was sent in, but %h came out", inSample, scob);
        else 
            return;
    end
endtask // meanB_a

task automatic meanF_a();
    logic[N*OSR-1:0] inSample;
    if(rst) begin
        inSample = inShift;
        repeat(3*depth+1) @(posedge clk);
        if(sf_delay != inSample)
            $error("Forward mean sample was misplaced!! %h was sent in, but %h came out", inSample, sf_delay);
        else 
            return;
    end
endtask // meanF_a

always @(posedge clkDS) 
    lookahead_a();

always @(posedge clkDS)
    meanB_a();

always @(posedge clkDS)
    meanF_a();

endmodule

`endif