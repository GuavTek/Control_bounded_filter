`ifndef TOPBATCHFIX_PROP_SV_
`define TOPBATCHFIX_PROP_SV_

`include "../sv/TopBatchFix.sv"
`include "../sv/Data/Coefficients_Fixedpoint.sv"

module Batch_Fixed_prop #(
    parameter depth = 32,
    parameter DSR = 1,
    parameter n_mant = 8,
    parameter n_int = 23
) (
    in,
    rst, clk, clkDS, valid,
    out,
    dBatCount, dBatCountRev, delayBatCount, delayBatCountRev, 
    cyclePulse, regProp,
    cycle, cycleLH, cycleIdle, cycleCalc, delayCycle,
    inShift,
    slh, scob, sf_delay, scof,
    finF, finB, finResult, partMemF, partMemB,
    partResF, partResB
);
    import Coefficients_Fx::*;
    localparam int DownSampleDepth = $ceil((0.0 + depth) / DSR);
    localparam SampleWidth = N*DSR; 
    localparam n_tot = n_int + n_mant;
    localparam int LUT_Layers = $clog2(int'($ceil((0.0 + SampleWidth)/`MAX_LUT_SIZE)));
    localparam int LUT_Delay = $ceil((0.0 + LUT_Layers)/`COMB_ADDERS);

    input wire [N-1:0] in;
    input logic rst, clk, clkDS, valid;
    input logic[`OUT_WIDTH-1:0] out;
    input logic[$clog2(DownSampleDepth)-1:0] dBatCount, dBatCountRev, delayBatCount[LUT_Delay + 2:0], delayBatCountRev[LUT_Delay + 2:0];
    input logic cyclePulse, regProp;
    input logic[1:0] cycle, cycleLH, cycleIdle, cycleCalc, delayCycle[LUT_Delay + 2:0];
    input logic[N*DSR-1:0] inShift;
    input logic[N*DSR-1:0] slh, scob, sf_delay, scof;
    input logic[`OUT_WIDTH-1:0] finF, finB, finResult, partMemF, partMemB;
    input logic signed[n_mant+n_int:0] partResF[N], partResB[N];

    property continuity_p;
        1 |=> $abs($abs(out) - $abs($past(out))) * 2.0**(-n_mant) < 0.3;
    endproperty

    task automatic lookahead_a(input logic[N*DSR-1:0] inSample);
        if(slh != inSample)
            $error("Lookahead sample was misplaced!! %h was sent in, but %h came out. Index %d", inSample, slh, dBatCountRev);
    endtask // lookahead_a

    property lookahead_p;
        int delay;
        logic[N*DSR-1:0] inSample;
        1 |-> (1, delay=dBatCount) ##0 (1, inSample=inShift) ##[0:DownSampleDepth+1] !cyclePulse ##[1:DownSampleDepth+1] (delay==(dBatCountRev)) ##0 (1, lookahead_a(inSample));
    endproperty

    task automatic meanB_a(input logic[N*DSR-1:0] inSample);
        if(scob != inSample)
            $error("Backward mean sample was misplaced!! %h was sent in, but %h came out", inSample, scob);
    endtask // meanB_a

    property meanB_p;
        int delay;
        logic[N*DSR-1:0] inSample;
        1 |-> (1, delay=dBatCount) ##0 (1, inSample=inShift) ##[2*DownSampleDepth:3*DownSampleDepth+1] !cyclePulse ##[1:DownSampleDepth+1] (delay==dBatCountRev) ##0 (1, meanB_a(inSample));
    endproperty

    task automatic meanF_a(input logic[N*DSR-1:0] inSample);
        if(sf_delay != inSample)
            $error("Forward mean sample was misplaced!! %h was sent in, but %h came out", inSample, sf_delay);
    endtask // meanF_a

    property meanF_p;
        int delay;
        logic[N*DSR-1:0] inSample;
        1 |-> (1, delay=dBatCount) ##0 (1, inSample=inShift) ##[2*DownSampleDepth:3*DownSampleDepth+1] !cyclePulse ##[1:DownSampleDepth+1] (delay==dBatCount) ##0 (1, meanF_a(inSample));
    endproperty

    task automatic calc_a(input logic[N*DSR-1:0] sampleB, sampleF);
        if(sf_delay != sampleB)
            $error("Forward sample %h does not match backward sample %h at position %d", sf_delay, sampleB, dBatCountRev);
        if(scob != sampleF)
            $error("Backward sample %h does not match forward sample %h at position %d", scob, sampleF, dBatCountRev);
    endtask // calc_a

    property calc_p;
        int delay;
        logic[N*DSR-1:0] sampleB, sampleF;
        (dBatCountRev >= (DownSampleDepth/2)) |-> (1, delay=dBatCount) ##0 (1, sampleB=scob) ##0 (1, sampleF=sf_delay)  ##[0:DownSampleDepth+1] (delay==dBatCountRev) ##0 (1, calc_a(sampleB, sampleF));
    endproperty

    task automatic resF_a(input logic[`OUT_WIDTH-1:0] resultSample);
        if (resultSample != finF)
            $error("Forward result misplaced!! %h was sent in, but %h came out", resultSample, finF);
    endtask

    property resF_p;
        int delay;
        logic[`OUT_WIDTH-1:0] resSample;
        1 |-> (1, delay=delayBatCount[LUT_Delay + 2]) ##0 (1, resSample=partMemF) ##[0:DownSampleDepth+1] (delay==delayBatCount[LUT_Delay + 1]) ##1 (1, resF_a(resSample));
    endproperty

    task automatic resB_a(input logic[`OUT_WIDTH-1:0] resultSample);
        if (resultSample != finB)
            $error("Backward result misplaced!! %h was sent in, but %h came out. Index %d", resultSample, finB, delayBatCountRev[LUT_Delay + 1]);
    endtask

    property resB_p;
        int delay;
        logic[`OUT_WIDTH-1:0] resSample;
        1 |-> (1, delay=delayBatCount[LUT_Delay + 2]) ##0 (1, resSample=partMemB) ##[0:DownSampleDepth+1] !$stable(delayCycle[LUT_Delay + 1]) ##[0:DownSampleDepth+1] (delay==delayBatCountRev[LUT_Delay + 1]) ##1 (1, resB_a(resSample));
    endproperty

    assert property (@(negedge clkDS) disable iff(!rst) lookahead_p)
    else $warning("Ooops! assertion failed");

    assert property (@(negedge clkDS) disable iff(!rst) meanB_p)
    else $warning("Ooops! assertion failed");

    assert property (@(negedge clkDS) disable iff(!rst) meanF_p)
    else $warning("Ooops! assertion failed");
    
    assert property (@(negedge clkDS) disable iff(!rst) calc_p)
    else $warning("Ooops! assertion failed");

    assert property (@(negedge clkDS) disable iff(!rst) resF_p)
    else $warning("Ooops! assertion failed");

    assert property (@(negedge clkDS) disable iff(!rst) resB_p)
    else $warning("Ooops! assertion failed");

    assert property (@(negedge clkDS) disable iff(!rst) continuity_p)
    else $warning("Potential discontinuity!! Output changed by %f, at cycle %1d index %4d", out * 2.0**(-n_mant) - $past(out * 2.0**(-n_mant)), delayCycle[1], delayBatCount[1] );

endmodule

`endif