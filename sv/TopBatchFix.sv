`ifndef TOPBATCHFIX_SV_
`define TOPBATCHFIX_SV_

// n_int 9
// 60dB n_mant 14
// 70dB n_mant 16

`include "Util.sv"
`include "Data/Coefficients_Fixedpoint.sv"
`include "FixPU.sv"
`include "CFixPU.sv"
`include "FixRecursionModule.sv"
`include "FixLUT.sv"
`include "FixToFix.sv"

`define MAX_LUT_SIZE 6
`define COMB_ADDERS 1
`define OUT_WIDTH 14

module Batch_Fixed_top #(
    parameter depth = 180,
    parameter OSR = 12,
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
    import Coefficients_Fx::*;
    localparam int DownSampleDepth = $ceil((0.0 + depth) / OSR);
    localparam SampleWidth = N*OSR; 
    localparam n_tot = n_int + n_mant;
    localparam int LUT_Layers = $clog2(int'($ceil((0.0 + SampleWidth)/`MAX_LUT_SIZE)));
    localparam int LUT_Delay = $ceil((0.0 + LUT_Layers)/`COMB_ADDERS);

    input wire [N-1:0] in;
    input logic rst, clk;
    output logic[`OUT_WIDTH-1:0] out;
    output logic valid;
    // Sample memory
    output logic[$clog2(4*DownSampleDepth)-1:0]  sampleAddrIn, sampleAddrOut1, sampleAddrOut2, sampleAddrOut3;
	output logic sampleClk, sampleWrite;
	output logic[N*OSR-1:0] sampleDataIn;
	input logic[N*OSR-1:0] sampleDataOut1, sampleDataOut2, sampleDataOut3;
    // Part result memory
    output logic[$clog2(2*DownSampleDepth)-1:0]  resAddrInF, resAddrInB, resAddrOutF, resAddrOutB;
	output logic resClkF, resClkB, resWriteF, resWriteB;
	output logic[`OUT_WIDTH-1:0] resDataInF, resDataInB;
	input logic[`OUT_WIDTH-1:0] resDataOutF, resDataOutB;

    // Downsampled clock
    logic[$clog2(OSR)-1:0] osrCount;      // Prescale counter
    logic clkDS;
    logic prevRst;
    generate
        if(OSR > 1) begin
            always @(posedge clk) begin
                if (!rst && prevRst)
                    osrCount = 0;
                else if (osrCount == (OSR-1)) begin
                    osrCount = 0;
                    clkDS = 1;
                end else
                    osrCount++;
                prevRst = rst;

                if (osrCount == OSR/2)
                    clkDS = 0;
                
            end
        end else begin
            assign clkDS = clk;
        end
    endgenerate 

    // Shifted input
    logic[SampleWidth-1:0] inShift, inSample;
    logic[$clog2(SampleWidth)-1:0] inSel;

    // Generates register if OSR > 1
    generate
        if (OSR > 1) begin
            always @(posedge clk) begin
                inSel = N*(OSR - osrCount)-1;
                inSample[inSel -: N] = in;
            end

            always @(posedge clkDS) begin
                inShift = inSample;
            end
        end else begin
            always @(posedge clk) begin
                inShift = in;
            end
        end
    endgenerate

    // Counters for batch cycle
    logic[$clog2(DownSampleDepth)-1:0] dBatCount, dBatCountRev;     // counters for input samples
    logic[$clog2(DownSampleDepth)-1:0] delayBatCount[LUT_Delay + 2:0], delayBatCountRev[LUT_Delay + 2:0];
    generate
        for (genvar i = (LUT_Delay + 2); i > 0 ; i-- ) begin
            always @(posedge clkDS) begin
                delayBatCount[i] = delayBatCount[i - 1];
                delayBatCountRev[i] = delayBatCountRev[i - 1];
            end
        end
    endgenerate
    
    always @(posedge clkDS) begin
        delayBatCount[0] = dBatCount;
        delayBatCountRev[0] = dBatCountRev;
        if(!rst || (dBatCount == (DownSampleDepth-1))) begin
            dBatCount = 'b0;
            dBatCountRev = DownSampleDepth-1;
        end else begin
            dBatCount++;
            dBatCountRev--;
        end
    end

    // Count valid samples
    localparam ValidDelay = 4*DownSampleDepth + LUT_Delay + 2;
    logic[$clog2(ValidDelay):0] validCount;
    logic validResult, validCompute;
    always @(posedge clkDS) begin
        if(!rst) begin
            validCount = 'b0;
            validCompute = 'b0;
        end else if (!validResult) begin
            validCount++;
        end   
        validCompute = validCompute | (validCount == (3*DownSampleDepth + LUT_Delay));
    end

    assign validResult = validCount == ValidDelay;
    assign valid = validResult;

    // Is low when the cycle is ending
    logic cyclePulse;
    assign cyclePulse = !(dBatCount == (DownSampleDepth-1));

    // Recursion register propagation is delayed one half cycle
    logic[LUT_Delay:0] regProp;
    always @(negedge clkDS) begin
        regProp = regProp << 1;
        regProp[0] = cyclePulse;
    end

    // Counter for cycles
    logic[1:0] cycle, cycleLH, cycleIdle, cycleCalc;
    logic[1:0] delayCycle[LUT_Delay + 2:0];
    
    generate
        for (genvar i = (LUT_Delay + 2); i > 0 ; i-- ) begin
            always @(posedge clkDS) begin
                delayCycle[i] = delayCycle[i - 1];
            end
        end
    endgenerate

    always @(posedge clkDS) begin
        delayCycle[0] = cycle;
        if(!rst) begin
            cycle = 2'b00;
            cycleLH = 2'b11;
            cycleIdle = 2'b10;
            cycleCalc = 2'b01;
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
        scof = sf_delay;
        finF = finF_delay;
        finB = finB_delay;
        partMemB = scaledResB;
        partMemF = scaledResF;
        addrIn = {dBatCount, cycle};
        addrLH = {dBatCountRev, cycleLH};
        addrBR = {dBatCountRev, cycleCalc};
        addrFR = {dBatCount, cycleCalc};
        addrResIn = {delayBatCount[2 + LUT_Delay], delayCycle[2 + LUT_Delay][0]};
        addrResOutB = {delayBatCountRev[1 + LUT_Delay], !delayCycle[1 + LUT_Delay][0]};
        addrResOutF = {delayBatCount[1 + LUT_Delay], !delayCycle[1 + LUT_Delay][0]};
    end

    // Must reverse sample order for backward recursion LUTs
    wire[SampleWidth-1:0] slh_rev, scob_rev;
    generate
        genvar j;
        for (j = 0; j < OSR; j++ ) begin
            assign slh_rev[N*j +: N] = slh[N*(OSR-j-1) +: N];
            assign scob_rev[N*j +: N] = scob[N*(OSR-j-1) +: N];
        end
    endgenerate

    function automatic logic signed[SampleWidth-1:0][n_tot:0] GetFbr (int row);
        logic signed[SampleWidth-1:0][n_tot:0] tempArray;
        for (int i = 0; i < SampleWidth ; i++) begin
            tempArray[i][n_tot:0] = Fbr[row][i] >>> (COEFF_BIAS - n_mant);
        end
        return tempArray;
    endfunction

    function automatic logic signed[SampleWidth-1:0][n_tot:0] GetFbi (int row);
        logic signed[SampleWidth-1:0][n_tot:0] tempArray;
        for (int i = 0; i < SampleWidth ; i++) begin
            tempArray[i][n_tot:0] = Fbi[row][i] >>> (COEFF_BIAS - n_mant);
        end
        return tempArray;
    endfunction

    function automatic logic signed[SampleWidth-1:0][n_tot:0] GetFfr (int row);
        logic signed[SampleWidth-1:0][n_tot:0] tempArray;
        for (int i = 0; i < SampleWidth ; i++) begin
            tempArray[i][n_tot:0] = Ffr[row][i] >>> (COEFF_BIAS - n_mant);
        end
        return tempArray;
    endfunction

    function automatic logic signed[SampleWidth-1:0][n_tot:0] GetFfi (int row);
        logic signed[SampleWidth-1:0][n_tot:0] tempArray;
        for (int i = 0; i < SampleWidth ; i++) begin
            tempArray[i][n_tot:0] = Ffi[row][i] >>> (COEFF_BIAS - n_mant);
        end
        return tempArray;
    endfunction

    function logic signed[1:0][n_tot:0] cpow_fixed(logic signed[63:0] r, logic signed[63:0] i, int exp);
        logic signed[1:0][n_tot:0] result;
        logic signed[63:0] tempR, tempI;
        tempR = r;
        tempI = i;
        for (int j = 1; j < exp ; j++ ) begin
            //cmulcc.r = (a.r * b.r) - (a.i * b.i);
            //cmulcc.i = (a.i * b.r) + (a.r * b.i);
            logic signed[127:0] tempReal, tempImag;
            tempReal = (tempR * r) - (tempI * i);
            tempImag = (tempI * r) + (tempR * i);
            tempR = tempReal >>> COEFF_BIAS;
            tempI = tempImag >>> COEFF_BIAS;
        end
        result[0][n_tot:0] = tempR >>> (COEFF_BIAS - n_mant);
        result[1][n_tot:0] = tempI >>> (COEFF_BIAS - n_mant);
        return result;
    endfunction

    generate 
        genvar i;
        for (i = 0; i < N ; i++ ) begin
            logic signed[n_tot:0] CF_inR, CF_inI, CB_inR, CB_inI, LH_inR, LH_inI;
            
            localparam logic signed[SampleWidth-1:0][n_tot:0] tempFfr = GetFfr(i);
            localparam logic signed[SampleWidth-1:0][n_tot:0] tempFbr = GetFbr(i);
            localparam logic signed[SampleWidth-1:0][n_tot:0] tempFfi = GetFfi(i);
            localparam logic signed[SampleWidth-1:0][n_tot:0] tempFbi = GetFbi(i);

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

            localparam logic signed[1:0][n_tot:0] tempLb = cpow_fixed(Lbr[i], Lbi[i], OSR);
            localparam logic signed[1:0][n_tot:0] tempLf = cpow_fixed(Lfr[i], Lfi[i], OSR);

            logic signed[n_tot:0] LH_resR, LH_resI, CF_outR, CF_outI, CB_outR, CB_outI, WFR, WFI, WBR, WBI;
            // Lookahead 
            FixRecursionModule #(.factorR(tempLb[0][n_tot:0]), .factorI(tempLb[1][n_tot:0]), .n_int(n_int), .n_mant(n_mant)) LHR_ (
                .inR(LH_inR), .inI(LH_inI), .rst(regProp[LUT_Delay] & rst), .resetValR(0), .resetValI(0), .clk(clkDS), .outR(LH_resR), .outI(LH_resI)
                );
            // Compute
            logic signed[n_tot:0] RF_inR, RF_inI, RB_inR, RB_inI;
            assign RF_inR = validCompute ? CF_inR : 0;
            assign RB_inR = validCompute ? CB_inR : 0;
            assign RF_inI = validCompute ? CF_inI : 0;
            assign RB_inI = validCompute ? CB_inI : 0;
            FixRecursionModule #(.factorR(tempLf[0][n_tot:0]), .factorI(tempLf[1][n_tot:0]), .n_int(n_int), .n_mant(n_mant)) CFR_ (
                .inR(CF_inR), .inI(CF_inI), .rst(rst), .resetValR(0), .resetValI(0), .clk(clkDS), .outR(CF_outR), .outI(CF_outI)
                );
            FixRecursionModule #(.factorR(tempLb[0][n_tot:0]), .factorI(tempLb[1][n_tot:0]), .n_int(n_int), .n_mant(n_mant)) CBR_ (
                .inR(CB_inR), .inI(CB_inI), .rst(regProp[LUT_Delay] & rst), .resetValR(LH_resR), .resetValI(LH_resI), .clk(clkDS), .outR(CB_outR), .outI(CB_outI)
                );
            
            assign WFR = Wfr[i] >>> (COEFF_BIAS - n_mant);
            assign WFI = Wfi[i] >>> (COEFF_BIAS - n_mant);
            assign WBR = Wbr[i] >>> (COEFF_BIAS - n_mant);
            assign WBI = Wbi[i] >>> (COEFF_BIAS - n_mant);

            // Save in registers to reduce timing requirements
            logic signed[n_tot:0] F_outR, F_outI, B_outR, B_outI;
            always @(posedge clkDS) begin
                F_outR = CF_outR;
                F_outI = CF_outI;
                B_outR = CB_outR;
                B_outI = CB_outI;
            end

            logic signed[n_tot:0] resFR, resFI, resBR, resBI;
            CFixPU #(.op(MULT), .n_int(n_int), .n_mant(n_mant)) WFR_ (.AR(F_outR), .AI(F_outI), .BR(WFR), .BI(WFI), .clk(clkDS), .resultR(resFR), .resultI(resFI));
            CFixPU #(.op(MULT), .n_int(n_int), .n_mant(n_mant)) WBR_ (.AR(B_outR), .AI(B_outI), .BR(WBR), .BI(WBI), .clk(clkDS), .resultR(resBR), .resultI(resBI));



            // Final add
            logic signed[n_tot:0] forward, backward;
            always @(posedge clkDS) begin
                forward = resFR;
                backward = resBR;
            end

            if(i == 0) begin
                assign partResF[0] = forward;
                assign partResB[0] = backward;
            end else begin
                FixPU #(.op(ADD), .n_int(n_int), .n_mant(n_mant)) FINADDF (.A(partResF[i-1]), .B(forward), .clk(clkDS), .result(partResF[i]));
                FixPU #(.op(ADD), .n_int(n_int), .n_mant(n_mant)) FINADDB (.A(partResB[i-1]), .B(backward), .clk(clkDS), .result(partResB[i]));
            end
        end
    endgenerate

    // Final final result
    FixPU #(.op(ADD), .n_int(0), .n_mant(`OUT_WIDTH-1)) FINADD (.A(finF), .B(finB), .clk(clkDS), .result(finResult));
    always @(posedge clkDS) begin
        out = {!finResult[`OUT_WIDTH-1], finResult[`OUT_WIDTH-2:0]};
    end
endmodule

`endif