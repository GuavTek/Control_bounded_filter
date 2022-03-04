`ifndef BATCH_FXP_SV_
`define BATCH_FXP_SV_

// n_int 9
// 60dB n_mant 14
// 70dB n_mant 16

`include "Util.sv"
`include "FxpPU.sv"
`include "CFxpPU.sv"
`include "Recursion_Fxp.sv"
`include "LUT_Fxp.sv"
`include "Fxp_To_Fxp.sv"
`include "ClkDiv.sv"
`include "ValidCount.sv"
`include "InputReg.sv"

`define MAX_LUT_SIZE 6
`define COMB_ADDERS 1
`define OUT_WIDTH 14

module Batch_Fxp #(
    parameter depth = 180,
    parameter DSR = 12,
    parameter n_mant = 14,
    parameter n_int = 9
) (
    in, rst, clk, out, valid,
    // Sample memory
    sampleAddrIn, sampleAddrOut1, sampleAddrOut2, sampleAddrOut3,
	sampleClk, sampleWrite,	sampleDataIn, sampleDataOut1, sampleDataOut2, sampleDataOut3,
    // Part result memory
    resAddrInF, resAddrInB, resAddrOutF, resAddrOutB, resClkF, resClkB, resWriteF, resWriteB,
	resDataInF, resDataInB, resDataOutF, resDataOutB
);
    import Coefficients_Fx::N;
    import Coefficients_Fx::M;
    
    localparam int DownSampleDepth = $ceil((0.0 + depth) / DSR);
    localparam SampleWidth = M*DSR; 
    localparam n_tot = n_int + n_mant;
    localparam int LUT_Layers = $clog2(int'($ceil((0.0 + SampleWidth)/`MAX_LUT_SIZE)));
    localparam int LUT_Delay = $floor((0.0 + LUT_Layers)/`COMB_ADDERS) + 1;

    input wire [M-1:0] in;
    input logic rst, clk;
    output logic[`OUT_WIDTH-1:0] out;
    output logic valid;
    // Sample memory
    output logic[$clog2(4*DownSampleDepth)-1:0]  sampleAddrIn, sampleAddrOut1, sampleAddrOut2, sampleAddrOut3;
	output logic sampleClk, sampleWrite;
	output logic[M*DSR-1:0] sampleDataIn;
	input logic[M*DSR-1:0] sampleDataOut1, sampleDataOut2, sampleDataOut3;
    // Part result memory
    output logic[$clog2(2*DownSampleDepth)-1:0]  resAddrInF, resAddrInB, resAddrOutF, resAddrOutB;
	output logic resClkF, resClkB, resWriteF, resWriteB;
	output logic[`OUT_WIDTH-1:0] resDataInF, resDataInB;
	input logic[`OUT_WIDTH-1:0] resDataOutF, resDataOutB;

    // Downsampled clock
    logic[$clog2(DSR)-1:0] divCnt;
    logic clkDS;
    ClkDiv #(.DSR(DSR)) ClkDivider (.clkIn(clk), .rst(rst), .clkOut(clkDS), .cntOut(divCnt));
    
    // Count valid samples
    localparam validTime = 5*DownSampleDepth;
    localparam validComp = 3*DownSampleDepth + LUT_Delay;
    logic validCompute;
    ValidCount #(.TopVal(validTime), .SecondVal(validComp)) vc1 (.clk(clkDS), .rst(rst), .out(valid), .out2(validCompute));

    // Input register
    logic[SampleWidth-1:0] inShift;
    InputReg #(.M(M), .DSR(DSR)) inReg (.clk(clk), .pos(divCnt), .in(in), .out(inShift));

    logic[SampleWidth-1:0] inSample;
    always @(posedge clkDS) begin
        inSample <= inShift;
    end

    // Counters for batch cycle
    logic[$clog2(DownSampleDepth)-1:0] batCnt, batCntRev;
    logic cyclePulse;
    always @(posedge clkDS, negedge rst) begin
        if(!rst) begin
            batCnt <= 'b0;
            batCntRev <= DownSampleDepth-1;
        end else if(!cyclePulse) begin
            batCnt <= 'b0;
            batCntRev <= DownSampleDepth-1;
        end else begin
            batCnt <= batCnt + 1;
            batCntRev <= batCntRev - 1;
        end
    end

    // Is low when the cycle is ending
    assign cyclePulse = !(batCnt == (DownSampleDepth-1));

    // Counter for cycles
    logic[1:0] cycle, cycleLH, cycleIdle, cycleCalc;
    always @(posedge clkDS, negedge rst) begin
        if(!rst) begin
            cycle <= 2'b00;
            cycleLH <= 2'b11;
            cycleIdle <= 2'b10;
            cycleCalc <= 2'b01;
        end else if(!cyclePulse) begin
            cycleCalc <= cycleCalc + 1;
            cycleIdle <= cycleIdle + 1;
            cycleLH <= cycleLH + 1;
            cycle <= cycle + 1;
        end   
    end

    // Sample storage
    logic[SampleWidth-1:0] slh, scob, sf_delay, scof;
    logic[$clog2(4*DownSampleDepth)-1:0] addrIn, addrLH, addrBR, addrFR;
    assign sampleClk = clkDS;
    // Write sample to memory
    assign sampleWrite = 1'b1;
    assign sampleDataIn = inSample;
    assign sampleAddrIn = addrIn;
    // Read lookahead sample
    assign slh = sampleDataOut1;
    assign sampleAddrOut1 = addrLH;
    // Read forward recursion sample
    assign sf_delay = sampleDataOut2;
    assign sampleAddrOut2 = addrFR;
    // Read backward recursion sample
    assign scob = sampleDataOut3;
    assign sampleAddrOut3 = addrBR;
    
    // Partial result storage
    logic signed [`OUT_WIDTH-1:0] finF, finB, finResult, finF_delay, finB_delay, partMemB, partMemF;
    logic[$clog2(2*DownSampleDepth)-1:0] addrResIn, addrResOutB, addrResOutF;
    // Backward results
    assign resClkB = clkDS;
    assign resWriteB = 1'b1;
    assign resDataInB = partMemB;
    assign resAddrInB = addrResIn;
    assign finB_delay = resDataOutB;
    assign resAddrOutB = addrResOutB;
    // Forward results
    assign resClkF = clkDS;
    assign resWriteF = 1'b1;
    assign resDataInF = partMemF;
    assign resAddrInF = addrResIn;
    assign finF_delay = resDataOutF;
    assign resAddrOutF = addrResOutF;

    // Outputs from generate blocks
    logic signed[n_tot:0] forwardResult, backwardResult;

    // Scale results
    logic signed[`OUT_WIDTH-1:0] scaledResB, scaledResF;
    Fxp_To_Fxp #(.n_int_in(n_int), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) ResultScalerB (.in( backwardResult ), .out( scaledResB ) );
    Fxp_To_Fxp #(.n_int_in(n_int), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) ResultScalerF (.in( forwardResult ), .out( scaledResF ) );

    // Addresses for result memory must be delayed
    logic[$clog2(DownSampleDepth)-1:0] resBatCnt, resBatCntRev;
    logic[1:0] resCycle;
    Delay #(.size($clog2(DownSampleDepth)), .delay(LUT_Delay+3)) BatchCnt_Delay (.in(batCnt), .clk(clkDS), .out(resBatCnt));
    Delay #(.size($clog2(DownSampleDepth)), .delay(LUT_Delay+3)) BatchCntRev_Delay (.in(batCntRev), .clk(clkDS), .out(resBatCntRev)); 
    Delay #(.size(2), .delay(LUT_Delay+3)) Cycle_Delay (.in(cycle), .clk(clkDS), .out(resCycle)); 

    // Synchronize to clock
    always @(posedge clkDS) begin
        scof <= sf_delay;
        finF <= finF_delay;
        finB <= finB_delay;
        partMemB <= scaledResB;
        partMemF <= scaledResF;
        addrIn <= {batCnt, cycle};
        addrLH <= {batCntRev, cycleLH};
        addrBR <= {batCntRev, cycleCalc};
        addrFR <= {batCnt, cycleCalc};
        addrResIn <= {resBatCnt, resCycle[0]};
        addrResOutB <= {resBatCntRev, !resCycle[0]};
        addrResOutF <= {resBatCnt, !resCycle[0]};
    end

    // Register propagation for lookahead recursion is delayed
    logic regProp;
    Delay #(.size(1), .delay(LUT_Delay)) RegPropagate_Delay (.in(cyclePulse), .clk(clkDS), .out(regProp)); 

    // Generate backward recursion
    LookaheadRecursion #(
        .N(N), .M(M), .DSR(DSR), .n_int(n_int), .n_mant(n_mant), .lut_size(`MAX_LUT_SIZE), .lut_comb(1), .adders_comb(`COMB_ADDERS) ) AheadRec (
        .inSample(scob), .lookaheadSample(slh), .clkSample(clkDS), .clkResult(clkDS), .rst(rst), .validIn(validCompute), .propagate(regProp), .result(backwardResult) 
    );
    
    // Generate forward recursion
    LookbackRecursion #(
        .N(N), .M(M), .DSR(DSR), .n_int(n_int), .n_mant(n_mant), .lut_size(`MAX_LUT_SIZE), .lut_comb(1), .adders_comb(`COMB_ADDERS) ) BackRec (
        .inSample(scof), .clkSample(clkDS), .clkResult(clkDS), .rst(rst), .validIn(validCompute), .result(forwardResult) 
    );

    // Final final result
    FxpPU #(.op(FPU_p::ADD), .n_int(0), .n_mant(`OUT_WIDTH-1)) FINADD (.A(finF), .B(finB), .clk(clkDS), .result(finResult));
    always @(posedge clkDS) begin
        out <= {!finResult[`OUT_WIDTH-1], finResult[`OUT_WIDTH-2:0]};
    end
endmodule

`endif