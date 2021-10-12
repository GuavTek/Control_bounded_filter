`ifndef TOPBATCH_SV_
`define TOPBATCH_SV_

`include "Util.sv"
`include "Data/Coefficients.sv"
`include "FPU.sv"
`include "CFPU.sv"
`include "RecursionModule.sv"
`include "LUT.sv"
`include "RAM.sv"

module Batch_top #(
    parameter depth = 32,
    parameter N = 3,
    parameter OSR = 1
) (
    input wire [N-1:0] in,
    input logic rst, clk,
    output floatType out,
    // Sample memory
    output logic[$clog2(4*$rtoi($ceil(depth / OSR)))-1:0]  sampleAddrIn, sampleAddrOut1, sampleAddrOut2, sampleAddrOut3,
	output logic sampleClk, sampleWrite,
	output logic[N*OSR-1:0] sampleDataIn,
	input logic[N*OSR-1:0] sampleDataOut1, sampleDataOut2, sampleDataOut3,
    // Part result memory
    output logic[$clog2(2*$rtoi($ceil(depth / OSR)))-1:0]  resAddrInF, resAddrInB, resAddrOutF, resAddrOutB,
	output logic resClkF, resClkB, resWriteF, resWriteB,
	output logic[(`EXP_W + `MANT_W):0] resDataInF, resDataInB,
	input logic[(`EXP_W + `MANT_W):0] resDataOutF, resDataOutB
);
    import Coefficients::*;
    localparam DownSampleDepth = $rtoi($ceil(depth / OSR));
    localparam SampleWidth = N*OSR; 

    // Downsampled clock
    logic[$clog2(OSR):0] osrCount;      // Prescale counter
    logic clkDS;
    generate
        if(OSR > 1) begin
            always @(posedge clk) begin
                if(!rst)
                    osrCount = 0;
                else
                    osrCount++;
                if (osrCount == OSR)
                    osrCount = 0;
            end

            // MSb of counter is prescaled clock, not symmetrical for all OSR
            // Rising edge when osrCount = 0
            assign clkDS = !osrCount[$clog2(OSR)];
        end else begin
            assign clkDS = clk;
        end
    endgenerate


    // Shifted input
    logic[N*OSR-1:0] inShift;

    // Generates shift register if OSR > 1
    generate
        if (OSR > 1) begin
            always @(posedge clk) begin
                inShift[N*OSR-1:N] = inShift[N*OSR-N-1:0];
                inShift[N-1:0] = in;
            end
        end else begin
            always @(posedge clk) begin
                inShift = in;
            end
        end
    endgenerate

    // Counters for batch cycle
    //logic[$clog2(depth)-1:0] batCount, batCountRev;      // counter for input samples
    logic[$clog2(DownSampleDepth)-1:0] dBatCount, dBatCountRev;     // downsampled counters
    logic[$clog2(DownSampleDepth)-1:0] delayBatCount[2:0], delayBatCountRev[2:0];
    always @(posedge clkDS) begin
        delayBatCount[2] = delayBatCount[1];
        delayBatCount[1] = delayBatCount[0];
        delayBatCount[0] = dBatCount;
        delayBatCountRev[2] = delayBatCountRev[1];
        delayBatCountRev[1] = delayBatCountRev[0];
        delayBatCountRev[0] = dBatCountRev;
        if(!rst || (dBatCount == (depth-1))) begin
            //batCount = 0;
            //batCountRev = depth-1;
            dBatCount = 0;
            dBatCountRev = DownSampleDepth-1;
        end else begin
            dBatCount++;
            dBatCountRev--;
        end
    end

    // Is low when the cycle is ending
    logic cyclePulse;
    assign cyclePulse = !(dBatCount == (DownSampleDepth-1));

    // Recursion register propagation is delayed one cycle
    logic regProp;
    always @(negedge clkDS) begin
        regProp = cyclePulse;
    end

    // Counter for cycles
    logic[1:0] cycle, cycleLH, cycleIdle, cycleCalc;
    logic[1:0] delayCycle[2:0];
    always @(posedge clkDS) begin
        delayCycle[2] = delayCycle[1];
        delayCycle[1] = delayCycle[0];
        delayCycle[0] = cycle;
        if(!rst) begin
            cycle = 0;
            cycleLH = 3;
            cycleIdle = 2;
            cycleCalc = 1;
        end else if(!cyclePulse) begin
            cycleCalc = cycleIdle;
            cycleIdle = cycleLH;
            cycleLH = cycle;
            cycle++;
        end   
    end

    // Sample storage
    logic[SampleWidth-1:0] slh, scob, sf_delay, scof;
    logic[$clog2(4*DownSampleDepth)-1:0] addrIn, addrLH, addrBR, addrFR;
    assign sampleClk = clkDS;
    assign sampleWrite = 'b1;
    assign sampleDataIn = inShift;
    assign sampleAddrIn = addrIn;
    assign slh = sampleDataOut1;
    assign sf_delay = sampleDataOut2;
    assign scob = sampleDataOut3;
    assign sampleAddrOut1 = addrLH;
    assign sampleAddrOut2 = addrFR;
    assign sampleAddrOut3 = addrBR;

    // Outputs from generate blocks
    floatType partResF[N], partResB[N];

    // Partial result storage
    floatType finF, finB, finResult, finF_delay, finB_delay, partMemB, partMemF;
    logic[$clog2(2*DownSampleDepth)-1:0] addrResIn, addrResOutB, addrResOutF;
    assign resClkB = clkDS;
    assign resWriteB = 'b1;
    assign resDataInB = partMemB;
    assign resAddrInB = addrResIn;
    assign finB_delay = resDataOutB;
    assign resAddrOutB = addrResOutB;
    assign resClkF = clkDS;
    assign resWriteF = 'b1;
    assign resDataInF = partMemF;
    assign resAddrInF = addrResIn;
    assign finF_delay = resDataOutF;
    assign resAddrOutF = addrResOutF;

    always @(posedge clkDS) begin
        scof = sf_delay;
        finF = finF_delay;
        finB = finB_delay;
        partMemB = partResB[N-1];
        partMemF = partResF[N-1];
        addrIn = {dBatCount, cycle};
        addrLH = {dBatCountRev, cycleLH};
        addrBR = {dBatCountRev, cycleCalc};
        addrFR = {dBatCount, cycleCalc};
        addrResIn = {delayBatCount[2], delayCycle[2][0]};
        addrResOutB = {delayBatCountRev[1], !delayCycle[1][0]};
        addrResOutF = {delayBatCount[1], !delayCycle[1][0]};
    end

    genvar i;
    generate 
        for (i = 0; i < N ; i++ ) begin : CalculationBlock
            // Lookahead
            complex LH_res, LH_in;
                LUT #(.size(SampleWidth), .fact(Fbr[i][0:N-1])) LHLR_ (.sel(slh_rev), .result(LH_in.r));
                LUT #(.size(SampleWidth), .fact(Fbi[i][0:N-1])) LHLI_ (.sel(slh_rev), .result(LH_in.i));
            RecursionModule #(.factorR(Lbr[i]**OSR), .factorI(Lbi[i]**OSR)) LHR_ (.in(LH_in), .rst(regProp & rst), .resetVal({rtof(0.0), rtof(0.0)}), .clk(clkDS), .out(LH_res));

            // Compute
            complex CF_in, CB_in, CF_out, CB_out, WF, WB; 
            LUT #(.size(SampleWidth), .fact(Ffr[i][0:N-1])) CFLR_ (.sel(scof), .result(CF_in.r));
            LUT #(.size(SampleWidth), .fact(Ffi[i][0:N-1])) CFLI_ (.sel(scof), .result(CF_in.i));
            LUT #(.size(SampleWidth), .fact(Fbr[i][0:N-1])) CBLR_ (.sel(scob), .result(CB_in.r));
            LUT #(.size(SampleWidth), .fact(Fbi[i][0:N-1])) CBLI_ (.sel(scob), .result(CB_in.i));
            RecursionModule #(.factorR(Lfr[i]**OSR), .factorI(Lfi[i]**OSR)) CFR_ (.in(CF_in), .rst(rst), .resetVal({rtof(0.0), rtof(0.0)}), .clk(clkDS), .out(CF_out));
            RecursionModule #(.factorR(Lbr[i]**OSR), .factorI(Lbi[i]**OSR)) CBR_ (.in(CB_in), .rst(regProp & rst), .resetVal(LH_res), .clk(clkDS), .out(CB_out));
            assign WF.r = rtof(Wfr[i]);
            assign WF.i = rtof(Wfi[i]);
            assign WB.r = rtof(Wbr[i]);
            assign WB.i = rtof(Wbi[i]);

            // Save in registers to reduce timing requirements
            complex F_out, B_out;
            always @(posedge clkDS) begin
                F_out = CF_out;
                B_out = CB_out;
            end

            complex resF, resB;
            CFPU #(.op(MULT)) WFR_ (.A(F_out), .B(WF), .result(resF));
            CFPU #(.op(MULT)) WBR_ (.A(B_out), .B(WB), .result(resB));

            // Final add
            floatType forward, backward;
            always @(posedge clkDS) begin
                forward = resF.r;
                backward = resB.r;
            end

            if(i == 0) begin
                assign partResF[0] = forward;
                assign partResB[0] = backward;
            end else begin
                FPU #(.op(ADD)) FINADDF (.A(partResF[i-1]), .B(forward), .result(partResF[i]));
                FPU #(.op(ADD)) FINADDB (.A(partResB[i-1]), .B(backward), .result(partResB[i]));
            end
        end
    endgenerate

    // Final final result
    FPU #(.op(ADD)) FINADD (.A(finF), .B(finB), .result(finResult));
    always @(posedge clkDS) begin
        out = finResult;
    end
endmodule

`endif