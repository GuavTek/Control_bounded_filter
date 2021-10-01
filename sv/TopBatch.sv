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
    output floatType out
);
    import Coefficients::*;
    localparam DownSampleDepth = $rtoi($ceil(depth / OSR));
    localparam LUTdepth = N*OSR; 

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
    logic[$clog2(depth)-1:0] batCount, batCountRev;      // counter for input samples
    logic[$clog2(DownSampleDepth)-1:0] dBatCount, dBatCountRev;     // downsampled counters
    logic[$clog2(OSR):0] osrCount;      // Prescale counter
    always @(posedge clk) begin
        if(!rst || (batCount == (depth-1))) begin
            batCount = 0;
            batCountRev = depth-1;
            dBatCount = 0;
            dBatCountRev = DownSampleDepth-1;
            osrCount = 0;
        end else begin
            batCount++;
            batCountRev--;
            osrCount++;
            if (osrCount == OSR) begin
                dBatCountRev--;
                dBatCount++;
                osrCount = 0;
            end 
        end
    end

    // Is low when the cycle is ending
    logic cyclePulse;
    assign cyclePulse = !(batCount == (depth-1));

    // Recursion register propagation is delayed one cycle
    logic regProp;
    always @(posedge clk) begin
        regProp = cyclePulse;
    end

    // Counter for cycles
    logic[1:0] cycle, cycleLH, cycleIdle, cycleCalc;
    always @(posedge clk) begin
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
    
    // Downsampled clock
    logic clkDS;
    generate
        if(OSR > 1) begin
            // MSb of counter is prescaled clock, not symmetrical for all OSR
            // Rising edge when osrCount = 0
            assign clkDS = !osrCount[$clog2(OSR)];
        end else begin
            assign clkDS = clk;
        end
    endgenerate

    // Sample storage
    logic[N*OSR-1:0] slh, scob, sf_delay, scof;
    logic[$clog2(4*DownSampleDepth)-1:0] addrIn, addrLH, addrBR, addrFR;
    assign addrIn = {dBatCount, cycle};
    assign addrLH = {dBatCountRev, cycleLH};
    assign addrBR = {dBatCountRev, cycleCalc};
    assign addrFR = {dBatCount, cycleCalc};
    RAM_triple #(.depth(4*DownSampleDepth), .d_width(N*OSR)) sample (.clk(clkDS), .write(1), .dataIn(inShift), .addrIn(addrIn), 
            .dataOut1(slh), .dataOut2(sf_delay), .dataOut3(scob), .addrOut1(addrLH), .addrOut2(addrFR), .addrOut3(addrBR));

    always @(posedge clkDS) begin
        scof = sf_delay;
    end

    // Outputs from generate blocks
    floatType partResF[N], partResB[N];

    genvar i;
    generate 
        for (i = 0; i < N ; i++ ) begin : CalculationBlock
            // Lookahead
            complex LH_res, LH_in;
            LUT #(.size(LUTdepth), .re(Fbr[i][0:LUTdepth-1]), .im(Fbi[i][0:LUTdepth-1])) LHL_ (.sel(slh), .result(LH_in));
            RecursionModule #(.factorR(Lbr[i]**OSR), .factorI(Lbi[i]**OSR)) LHR_ (.in(LH_in), .rst(regProp & rst), .resetVal(LH_in), .clk(clkDS), .out(LH_res));

            // Compute
            complex CF_in, CB_in, CF_out, CB_out, WF, WB; 
            LUT #(.size(LUTdepth), .re(Ffr[i][0:LUTdepth-1]), .im(Ffi[i][0:LUTdepth-1])) CFL_ (.sel(scof), .result(CF_in));
            LUT #(.size(LUTdepth), .re(Fbr[i][0:LUTdepth-1]), .im(Fbi[i][0:LUTdepth-1])) CBL_ (.sel(scob), .result(CB_in));
            RecursionModule #(.factorR(Lfr[i]**OSR), .factorI(Lfi[i]**OSR)) CFR_ (.in(CF_in), .rst(rst), .resetVal(CF_in), .clk(clkDS), .out(CF_out));
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

    // Partial result storage
    floatType finF, finB, finResult;
    RAM_single #(.depth(2*DownSampleDepth), .d_width($bits(partResF[0]))) calcB (.clk(clkDS), .write(1), .dataIn(partResB[N-1]), .addrIn({dBatCount, cycle[0]}),
            .dataOut(finB), .addrOut({dBatCountRev, !cycle[0]}));
    RAM_single #(.depth(2*DownSampleDepth), .d_width($bits(partResF[0]))) calcF (.clk(clkDS), .write(1), .dataIn(partResF[N-1]), .addrIn({dBatCount, cycle[0]}),
            .dataOut(finF), .addrOut({dBatCount, !cycle[0]}));

    FPU #(.op(ADD)) FINADD (.A(finF), .B(finB), .result(finResult));

    // Final final result
    always @(posedge clkDS) begin
        out = finResult;
    end
endmodule

`endif