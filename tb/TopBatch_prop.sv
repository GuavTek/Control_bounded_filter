`ifndef TOPBATCH_PROP_SV_
`define TOPBATCH_PROP_SV_

`include "../sv/TopBatch.sv"
`include "../sv/Data/Coefficients.sv"

module Batch_top_prop #(
    parameter depth = 32,
    parameter OSR = 1
) (
    input wire [Coefficients::N-1:0] in,
    input logic rst, clk, clkDS,
    input floatType out,
    input logic[$clog2($rtoi($ceil(depth / OSR)))-1:0] dBatCount, dBatCountRev, delayBatCount[2:0], delayBatCountRev[2:0], 
    input logic cyclePulse, regProp,
    input logic[1:0] cycle, cycleLH, cycleIdle, cycleCalc, delayCycle[2:0],
    input logic[Coefficients::N*OSR-1:0] inShift,
    input logic[Coefficients::N*OSR-1:0] slh, scob, sf_delay, scof,
    input floatType finF, finB, finResult, partMemF, partMemB,
    input floatType partResF[Coefficients::N], partResB[Coefficients::N]
);
    import Coefficients::N;
    localparam DownSampleDepth = $rtoi($ceil(depth / OSR));

    

    property continuity_p;
        1 |=> absr(absr(ftor(finResult)) - absr(ftor($past(finResult)))) < 0.3;
    endproperty

    task automatic lookahead_a(input logic[N*OSR-1:0] inSample);
        if(slh != inSample)
            $error("Lookahead sample was misplaced!! %h was sent in, but %h came out. Index %d", inSample, slh, dBatCountRev);
    endtask // lookahead_a

    property lookahead_p;
        int delay;
        logic[N*OSR-1:0] inSample;
        1 |-> (1, delay=dBatCount) ##0 (1, inSample=inShift) ##[0:DownSampleDepth] !cyclePulse ##[1:DownSampleDepth] (delay==(dBatCountRev)) ##0 (1, lookahead_a(inSample));
    endproperty

    task automatic meanB_a(input logic[N*OSR-1:0] inSample);
        if(scob != inSample)
            $error("Backward mean sample was misplaced!! %h was sent in, but %h came out", inSample, scob);
    endtask // meanB_a

    property meanB_p;
        int delay;
        logic[N*OSR-1:0] inSample;
        1 |-> (1, delay=dBatCount) ##0 (1, inSample=inShift) ##[2*DownSampleDepth:3*DownSampleDepth] !cyclePulse ##[1:DownSampleDepth] (delay==dBatCountRev) ##0 (1, meanB_a(inSample));
    endproperty

    task automatic meanF_a(input logic[N*OSR-1:0] inSample);
        if(sf_delay != inSample)
            $error("Forward mean sample was misplaced!! %h was sent in, but %h came out", inSample, sf_delay);
    endtask // meanF_a

    property meanF_p;
        int delay;
        logic[N*OSR-1:0] inSample;
        1 |-> (1, delay=dBatCount) ##0 (1, inSample=inShift) ##[2*DownSampleDepth:3*DownSampleDepth] !cyclePulse ##[1:DownSampleDepth] (delay==dBatCount) ##0 (1, meanF_a(inSample));
    endproperty

    task automatic calc_a(input logic[N*OSR-1:0] sampleB, sampleF);
        if(sf_delay != sampleB)
            $error("Forward sample %h does not match backward sample %h at position %d", sf_delay, sampleB, dBatCountRev);
        if(scob != sampleF)
            $error("Backward sample %h does not match forward sample %h at position %d", scob, sampleF, dBatCountRev);
    endtask // calc_a

    property calc_p;
        int delay;
        logic[N*OSR-1:0] sampleB, sampleF;
        (dBatCountRev >= (DownSampleDepth/2)) |-> (1, delay=dBatCount) ##0 (1, sampleB=scob) ##0 (1, sampleF=sf_delay)  ##[0:DownSampleDepth] (delay==dBatCountRev) ##0 (1, calc_a(sampleB, sampleF));
    endproperty

    task automatic resF_a(input floatType resultSample);
        if (resultSample != finF)
            $error("Forward result misplaced!! %h was sent in, but %h came out", resultSample, finF);
    endtask

    property resF_p;
        int delay;
        floatType resSample;
        1 |-> (1, delay=delayBatCount[2]) ##0 (1, resSample=partMemF) ##[0:DownSampleDepth] (delay==delayBatCount[1]) ##1 (1, resF_a(resSample));
    endproperty

    task automatic resB_a(input floatType resultSample);
        if (resultSample != finB)
            $error("Backward result misplaced!! %h was sent in, but %h came out. Index %d", resultSample, finB, delayBatCountRev[1]);
    endtask

    property resB_p;
        int delay;
        floatType resSample;
        1 |-> (1, delay=delayBatCount[2]) ##0 (1, resSample=partMemB) ##[0:DownSampleDepth] !$stable(delayCycle[1]) ##[0:DownSampleDepth] (delay==delayBatCountRev[1]) ##1 (1, resB_a(resSample));
    endproperty

    assert property (@(posedge !clkDS) disable iff(!rst) lookahead_p)
    else $warning("Ooops! assertion failed");

    assert property (@(posedge !clkDS) disable iff(!rst) meanB_p)
    else $warning("Ooops! assertion failed");

    assert property (@(posedge !clkDS) disable iff(!rst) meanF_p)
    else $warning("Ooops! assertion failed");
    
    assert property (@(posedge !clkDS) disable iff(!rst) calc_p)
    else $warning("Ooops! assertion failed");

    assert property (@(posedge !clkDS) disable iff(!rst) resF_p)
    else $warning("Ooops! assertion failed");

    assert property (@(posedge !clkDS) disable iff(!rst) resB_p)
    else $warning("Ooops! assertion failed");

    assert property (@(posedge !clkDS) disable iff(!rst) continuity_p)
    else $warning("Potential discontinuity!! Output changed by %f, at cycle %1d index %4d", absr(ftor(finResult)) - absr(ftor($past(finResult))), delayCycle[1], delayBatCount[1] );

endmodule

`endif