`ifndef TOPBATCHFIX_SV_
`define TOPBATCHFIX_SV_

// n_int 9
// 60dB n_mant 14
// 70dB n_mant 16

`include "Data/Coefficients_Fixedpoint.sv"
`include "Util.sv"
`include "FixPU.sv"
`include "CFixPU.sv"
`include "FixRecursionModule.sv"
`include "FixLUT.sv"
`include "FixToFix.sv"
`include "ClkDiv.sv"
`include "ValidCount.sv"
`include "InputReg.sv"

`define MAX_LUT_SIZE 6
`define COMB_ADDERS 1
`define OUT_WIDTH 14

module Batch_Fixed_top #(
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
    localparam int DownSampleDepth = $ceil((0.0 + depth) / DSR);
    localparam SampleWidth = N*DSR; 
    localparam n_tot = n_int + n_mant;
    localparam int LUT_Layers = $clog2(int'($ceil((0.0 + SampleWidth)/`MAX_LUT_SIZE)));
    localparam int LUT_Delay = $ceil((0.0 + LUT_Layers)/`COMB_ADDERS) + 1;

    input wire [N-1:0] in;
    input logic rst, clk;
    output logic[`OUT_WIDTH-1:0] out;
    output logic valid;
    // Sample memory
    output logic[$clog2(4*DownSampleDepth)-1:0]  sampleAddrIn, sampleAddrOut1, sampleAddrOut2, sampleAddrOut3;
	output logic sampleClk, sampleWrite;
	output logic[N*DSR-1:0] sampleDataIn;
	input logic[N*DSR-1:0] sampleDataOut1, sampleDataOut2, sampleDataOut3;
    // Part result memory
    output logic[$clog2(2*DownSampleDepth)-1:0]  resAddrInF, resAddrInB, resAddrOutF, resAddrOutB;
	output logic resClkF, resClkB, resWriteF, resWriteB;
	output logic[`OUT_WIDTH-1:0] resDataInF, resDataInB;
	input logic[`OUT_WIDTH-1:0] resDataOutF, resDataOutB;

    // Downsampled clock
    logic[$clog2(DSR)-1:0] dsrCount;      // Prescale counter
    logic clkDS;
    ClkDiv #(.DSR(DSR)) ClkDivider (.clkIn(clk), .rst(rst), .clkOut(clkDS), .cntOut(dsrCount));
    
    // Shifted input
    logic[SampleWidth-1:0] inShift, inSample;
    always @(posedge clkDS) begin
        inShift <= inSample;
    end

    InputReg #(.M(N), .DSR(DSR)) inReg (.clk(clk), .pos(dsrCount), .in(in), .out(inSample));


    // Counters for batch cycle
    logic[$clog2(DownSampleDepth)-1:0] dBatCount, dBatCountRev;     // counters for input samples
    logic[$clog2(DownSampleDepth)-1:0] delayBatCount[LUT_Delay + 2:0], delayBatCountRev[LUT_Delay + 2:0];
    
    // Is low when the cycle is ending
    logic cyclePulse;
    assign cyclePulse = !(dBatCount == (DownSampleDepth-1));

    generate
        for (genvar i = (LUT_Delay + 2); i > 0 ; i-- ) begin
            always @(posedge clkDS) begin
                delayBatCount[i] <= delayBatCount[i - 1];
                delayBatCountRev[i] <= delayBatCountRev[i - 1];
            end
        end
    endgenerate

    always @(posedge clkDS, negedge rst) begin
        delayBatCount[0] <= dBatCount;
        delayBatCountRev[0] <= dBatCountRev;
        if(!rst || !cyclePulse) begin
            dBatCount <= 'b0;
            dBatCountRev <= DownSampleDepth-1;
        end else begin
            dBatCount <= dBatCount + 1;
            dBatCountRev <= dBatCountRev - 1;
        end
    end

    // Count valid samples
    localparam validTime = 5*DownSampleDepth;
    localparam validComp = 3*DownSampleDepth + LUT_Delay;
    logic validCompute;
    ValidCount #(.TopVal(validTime), .SecondVal(validComp)) vc1 (.clk(clkDS), .rst(rst), .out(valid), .out2(validCompute));


    // Recursion register propagation is delayed one half cycle
    logic[LUT_Delay+2:0] regProp;
    always @(negedge clkDS) begin
        regProp <= regProp << 1;
        regProp[0] <= cyclePulse;
    end


    // Counter for cycles
    logic[1:0] cycle, cycleLH, cycleIdle, cycleCalc;
    logic[1:0] delayCycle[LUT_Delay + 2:0];
    
    generate
        for (genvar i = (LUT_Delay + 2); i > 0 ; i-- ) begin
            always @(posedge clkDS) begin
                delayCycle[i] <= delayCycle[i - 1];
            end
        end
    endgenerate

    always @(posedge clkDS, negedge rst) begin
        delayCycle[0] <= cycle;
        if(!rst) begin
            cycle <= 2'b00;
            cycleLH <= 2'b11;
            cycleIdle <= 2'b10;
            cycleCalc <= 2'b01;
        end else if(!cyclePulse) begin
            cycleCalc <= cycleIdle;
            cycleIdle <= cycleLH;
            cycleLH <= cycle;
            cycle <= cycle + 1;
        end   
    end

    // Sample storage
    logic[SampleWidth-1:0] slh, scob, sf_delay, scof;
    logic[$clog2(4*DownSampleDepth)-1:0] addrIn, addrLH, addrBR, addrFR;
    assign sampleClk = clkDS;
    assign sampleWrite = 1'b1;
    assign sampleDataIn = inShift;
    assign sampleAddrIn = addrIn;
    assign slh = sampleDataOut1;
    assign sf_delay = sampleDataOut2;
    assign scob = sampleDataOut3;
    assign sampleAddrOut1 = addrLH;
    assign sampleAddrOut2 = addrFR;
    assign sampleAddrOut3 = addrBR;

    // Outputs from generate blocks
    logic signed[n_tot:0] partResF[N], partResB[N];

    // Partial result storage
    logic signed [`OUT_WIDTH-1:0] finF, finB, finResult, finF_delay, finB_delay, partMemB, partMemF;
    logic[$clog2(2*DownSampleDepth)-1:0] addrResIn, addrResOutB, addrResOutF;
    assign resClkB = clkDS;
    assign resWriteB = 1'b1;
    assign resDataInB = partMemB;
    assign resAddrInB = addrResIn;
    assign finB_delay = resDataOutB;
    assign resAddrOutB = addrResOutB;
    assign resClkF = clkDS;
    assign resWriteF = 1'b1;
    assign resDataInF = partMemF;
    assign resAddrInF = addrResIn;
    assign finF_delay = resDataOutF;
    assign resAddrOutF = addrResOutF;

    // Scale results
    logic signed[`OUT_WIDTH-1:0] scaledResB, scaledResF;
    FixToFix #(.n_int_in(n_int), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) ResultScalerB (.in( partResB[N-1] ), .out( scaledResB ) );
    FixToFix #(.n_int_in(n_int), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) ResultScalerF (.in( partResF[N-1] ), .out( scaledResF ) );

    always @(posedge clkDS) begin
        scof <= sf_delay;
        finF <= finF_delay;
        finB <= finB_delay;
        partMemB <= scaledResB;
        partMemF <= scaledResF;
        addrIn <= {dBatCount, cycle};
        addrLH <= {dBatCountRev, cycleLH};
        addrBR <= {dBatCountRev, cycleCalc};
        addrFR <= {dBatCount, cycleCalc};
        addrResIn <= {delayBatCount[2 + LUT_Delay], delayCycle[2 + LUT_Delay][0]};
        addrResOutB <= {delayBatCountRev[2 + LUT_Delay], !delayCycle[2 + LUT_Delay][0]};
        addrResOutF <= {delayBatCount[2 + LUT_Delay], !delayCycle[2 + LUT_Delay][0]};
    end

    // Must reverse sample order for backward recursion LUTs
    wire[SampleWidth-1:0] slh_rev, scob_rev;
    generate
        genvar j;
        for (j = 0; j < DSR; j++ ) begin
            assign slh_rev[N*j +: N] = slh[N*(DSR-j-1) +: N];
            assign scob_rev[N*j +: N] = scob[N*(DSR-j-1) +: N];
        end
    endgenerate

    generate 
        genvar i;
        for (i = 0; i < N ; i++ ) begin
            logic signed[n_tot:0] CF_inR, CF_inI, CB_inR, CB_inI, LH_inR, LH_inI;
            
            localparam logic signed[SampleWidth-1:0][n_tot:0] tempFfr = GetConst #(.n_int(n_int), .n_mant(n_mant), .size(SampleWidth))::Ffr(i);
            localparam logic signed[SampleWidth-1:0][n_tot:0] tempFbr = GetConst #(.n_int(n_int), .n_mant(n_mant), .size(SampleWidth))::Fbr(i);
            localparam logic signed[SampleWidth-1:0][n_tot:0] tempFfi = GetConst #(.n_int(n_int), .n_mant(n_mant), .size(SampleWidth))::Ffi(i);
            localparam logic signed[SampleWidth-1:0][n_tot:0] tempFbi = GetConst #(.n_int(n_int), .n_mant(n_mant), .size(SampleWidth))::Fbi(i);

            FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFbr), .n_int(n_int), .n_mant(n_mant)) LH_LUTr (
                .sel(slh_rev), .clk(clkDS), .result(LH_inR)
                );

            FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFfr), .n_int(n_int), .n_mant(n_mant)) CF_LUTr (
                .sel(scof), .clk(clkDS), .result(CF_inR)
                );

            FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFbr), .n_int(n_int), .n_mant(n_mant)) CB_LUTr (
                .sel(scob_rev), .clk(clkDS), .result(CB_inR)
            );

            FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFbi), .n_int(n_int), .n_mant(n_mant)) LH_LUTi (
                .sel(slh_rev), .clk(clkDS), .result(LH_inI)
                );

            FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFfi), .n_int(n_int), .n_mant(n_mant)) CF_LUTi (
                .sel(scof), .clk(clkDS), .result(CF_inI)
                );

            FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFbi), .n_int(n_int), .n_mant(n_mant)) CB_LUTi (
                .sel(scob_rev), .clk(clkDS), .result(CB_inI)
            );

            localparam tempLbr = Coefficients_Fx::Lbr[i];
            localparam tempLbi = Coefficients_Fx::Lbi[i];
            localparam tempLfr = Coefficients_Fx::Lfr[i];
            localparam tempLfi = Coefficients_Fx::Lfi[i];
            localparam logic signed[1:0][n_tot:0] tempLb = GetConst #(.n_int(n_int), .n_mant(n_mant))::cpow(tempLbr, tempLbi, DSR);
            localparam logic signed[1:0][n_tot:0] tempLf = GetConst #(.n_int(n_int), .n_mant(n_mant))::cpow(tempLfr, tempLfi, DSR);
            localparam logic signed[n_tot:0] resetZero = 'b0;

            logic signed[n_tot:0] LH_resR, LH_resI, CF_outR, CF_outI, CB_outR, CB_outI, WFR, WFI, WBR, WBI;
            // Lookahead 
            FixRecursionModule #(.factorR(tempLb[0][n_tot:0]), .factorI(tempLb[1][n_tot:0]), .n_int(n_int), .n_mant(n_mant)) LHR_ (
                .inR(LH_inR), .inI(LH_inI), .rst(regProp[LUT_Delay] & rst), .resetValR(resetZero), .resetValI(resetZero), .clk(clkDS || !rst), .outR(LH_resR), .outI(LH_resI)
                );
            // Compute
            logic signed[n_tot:0] RF_inR, RF_inI, RB_inR, RB_inI;
            assign RF_inR = validCompute ? CF_inR : 0;
            assign RB_inR = validCompute ? CB_inR : 0;
            assign RF_inI = validCompute ? CF_inI : 0;
            assign RB_inI = validCompute ? CB_inI : 0;
            FixRecursionModule #(.factorR(tempLf[0][n_tot:0]), .factorI(tempLf[1][n_tot:0]), .n_int(n_int), .n_mant(n_mant)) CFR_ (
                .inR(RF_inR), .inI(RF_inI), .rst(rst), .resetValR(resetZero), .resetValI(resetZero), .clk(clkDS || !rst), .outR(CF_outR), .outI(CF_outI)
                );
            FixRecursionModule #(.factorR(tempLb[0][n_tot:0]), .factorI(tempLb[1][n_tot:0]), .n_int(n_int), .n_mant(n_mant)) CBR_ (
                .inR(RB_inR), .inI(RB_inI), .rst(regProp[LUT_Delay] & rst), .resetValR(LH_resR), .resetValI(LH_resI), .clk(clkDS || !rst), .outR(CB_outR), .outI(CB_outI)
                );
            
            assign WFR = GetConst #(.n_int(n_int), .n_mant(n_mant))::Wfr(i);
            assign WFI = GetConst #(.n_int(n_int), .n_mant(n_mant))::Wfi(i);
            assign WBR = GetConst #(.n_int(n_int), .n_mant(n_mant))::Wbr(i);
            assign WBI = GetConst #(.n_int(n_int), .n_mant(n_mant))::Wbi(i);

            // Save in registers to reduce timing requirements
            logic signed[n_tot:0] F_outR, F_outI, B_outR, B_outI;
            always @(posedge clkDS) begin
                F_outR <= CF_outR;
                F_outI <= CF_outI;
                B_outR <= CB_outR;
                B_outI <= CB_outI;
            end

            logic signed[n_tot:0] resFR, resFI, resBR, resBI;
            CFixPU #(.op(FPU_p::MULT), .n_int(n_int), .n_mant(n_mant)) WFR_ (.AR(F_outR), .AI(F_outI), .BR(WFR), .BI(WFI), .clk(clkDS), .resultR(resFR), .resultI(resFI));
            CFixPU #(.op(FPU_p::MULT), .n_int(n_int), .n_mant(n_mant)) WBR_ (.AR(B_outR), .AI(B_outI), .BR(WBR), .BI(WBI), .clk(clkDS), .resultR(resBR), .resultI(resBI));



            // Final add
            logic signed[n_tot:0] forward, backward;
            always @(posedge clkDS) begin
                forward <= resFR;
                backward <= resBR;
            end

            if(i == 0) begin
                assign partResF[0] = forward;
                assign partResB[0] = backward;
            end else begin
                FixPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) FINADDF (.A(partResF[i-1]), .B(forward), .clk(clkDS), .result(partResF[i]));
                FixPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) FINADDB (.A(partResB[i-1]), .B(backward), .clk(clkDS), .result(partResB[i]));
            end
        end
    endgenerate

    // Final final result
    FixPU #(.op(FPU_p::ADD), .n_int(0), .n_mant(`OUT_WIDTH-1)) FINADD (.A(finF), .B(finB), .clk(clkDS), .result(finResult));
    always @(posedge clkDS) begin
        out <= {!finResult[`OUT_WIDTH-1], finResult[`OUT_WIDTH-2:0]};
    end
endmodule

`endif