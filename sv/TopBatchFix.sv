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
    parameter OSR1 = 2,
    parameter OSR2 = 6,
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
    localparam OSR = OSR1 * OSR2;
    localparam int DownResultDepth = $ceil((0.0 + depth) / OSR);
    localparam int DownSampleDepth = DownResultDepth * OSR2;
    localparam SampleWidth = N*OSR1; 
    localparam n_tot = n_int + n_mant;
    localparam int LUT_Layers = $clog2(int'($ceil((0.0 + SampleWidth)/`MAX_LUT_SIZE)));
    localparam int LUT_Delay = $ceil((0.0 + LUT_Layers)/`COMB_ADDERS);
    localparam int Recursion_Delay = $ceil((0.0 + LUT_Delay)/OSR2);

    input wire [N-1:0] in;
    input logic rst, clk;
    output logic[`OUT_WIDTH-1:0] out;
    output logic valid;
    // Sample memory
    output logic[$clog2(4*DownSampleDepth)-1:0]  sampleAddrIn, sampleAddrOut1, sampleAddrOut2, sampleAddrOut3;
	output logic sampleClk, sampleWrite;
	output logic[SampleWidth-1:0] sampleDataIn;
	input logic[SampleWidth-1:0] sampleDataOut1, sampleDataOut2, sampleDataOut3;
    // Part result memory
    output logic[$clog2(2*DownResultDepth)-1:0]  resAddrInF, resAddrInB, resAddrOutF, resAddrOutB;
	output logic resClkF, resClkB, resWriteF, resWriteB;
	output logic[`OUT_WIDTH-1:0] resDataInF, resDataInB;
	input logic[`OUT_WIDTH-1:0] resDataOutF, resDataOutB;

    // Downsampled clocks
    logic[$clog2(OSR1)-1:0] osrCount1;
    logic[$clog2(OSR2)-1:0] osrCount2;      // Prescale counter
    logic clkDS, clkRecurse, prevRst1, prevRst2;
    generate
        if(OSR2 > 1) begin
            always @(posedge clkRecurse) begin
                if ((!rst && prevRst2) || (osrCount2 == (OSR2-1)))
                    osrCount2 = 'b0;
                else
                    osrCount2++;

                if (1)
                    prevRst2 = rst;

                if (osrCount2 == 0)
                    clkDS = 1;
                if (osrCount2 == OSR2/2)
                    clkDS = 0;
                
            end
        end else begin
            assign clkDS = clkRecurse;
            assign osrCount2 = 0;
        end

        if(OSR1 > 1) begin
            always @(posedge clk) begin
                if ((!rst && prevRst1) || (osrCount1 == (OSR1-1)))
                    osrCount1 = 'b0;
                else
                    osrCount1++;

                if (1)
                    prevRst1 = rst;

                if (osrCount1 == 0)
                    clkRecurse = 1;
                if (osrCount1 == OSR1/2)
                    clkRecurse = 0;
                
            end
        end else begin
            assign clkRecurse = clk;
        end
    endgenerate 

    // Shifted input
    logic[SampleWidth-1:0] inShift, inSample;
    logic[$clog2(SampleWidth)-1:0] inSel;

    // Generates register if OSR > 1
    generate
        if (OSR1 > 1) begin
            always @(posedge clk) begin
                inSel = N*(OSR1 - osrCount1)-1;
                inSample[inSel -: N] = in;
            end

            always @(posedge clkRecurse) begin
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
    logic[$clog2(DownResultDepth)-1:0] delayBatCount[Recursion_Delay + 4:0], delayBatCountRev[Recursion_Delay + 4:0], batCount, batCountRev;
    generate
        for (genvar i = (Recursion_Delay + 4); i > 0 ; i-- ) begin
            always @(posedge clkDS) begin
                delayBatCount[i] = delayBatCount[i - 1];
                delayBatCountRev[i] = delayBatCountRev[i - 1];
            end
        end
    endgenerate
    
    always @(posedge clkDS) begin
        delayBatCount[0] = batCount;
        delayBatCountRev[0] = batCountRev;
        if(!rst || (batCount == (DownResultDepth-1))) begin
            batCount = 'b0;
            batCountRev = DownResultDepth-1;
        end else begin
            batCount++;
            batCountRev--;
        end
    end

    always @(negedge clkRecurse) begin
        dBatCount = batCount * OSR2 + osrCount2;
        dBatCountRev = batCountRev * OSR2 - osrCount2 + OSR2-1; 
    end

    // Count valid samples
    localparam validTime = 4*DownResultDepth + Recursion_Delay + 5;
    logic[$clog2(validTime):0] validCount;
    logic validClk, validResult, validCompute;
    always @(posedge validClk, negedge rst) begin
        if(!rst) begin
            validCount = 'b0;
            validCompute = 'b0;
        end else begin
            validCount++;
            validCompute = validCompute | (validCount == (3*DownResultDepth + Recursion_Delay + 2));
        end        
    end

    assign validResult = validCount == validTime;
    assign validClk = clkDS && !validResult;
    assign valid = validResult;

    // Is low when the cycle is ending
    logic cyclePulse;
    assign cyclePulse = !(dBatCount == (DownSampleDepth-1));

    // Recursion register propagation is delayed one half cycle
    logic[LUT_Delay+2:0] regProp;
    always @(negedge clkRecurse) begin
        regProp = regProp << 1;
        regProp[0] = cyclePulse;
    end

    // Counter for cycles
    logic[1:0] cycle, cycleLH, cycleIdle, cycleCalc;
    logic[1:0] delayCycle[Recursion_Delay + 4:0];
    
    generate
        for (genvar i = (Recursion_Delay + 4); i > 0 ; i-- ) begin
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
    logic[$clog2(4*DownSampleDepth)-1:0] addrIn, addrLH, addrBR, addrFR, addrIn_t[3], addrLH_t[3], addrBR_t[3], addrFR_t[3];
    assign sampleClk = clkRecurse;
    assign sampleWrite = 1'b1;
    assign sampleDataIn = inShift;
    assign sampleAddrIn = addrIn;
    assign slh = sampleDataOut1;
    assign scof = sampleDataOut2;
    assign scob = sampleDataOut3;
    assign sampleAddrOut1 = addrLH;
    assign sampleAddrOut2 = addrFR;
    assign sampleAddrOut3 = addrBR;

    // Outputs from generate blocks
    logic signed[n_tot:0] partResF[N], partResB[N];

    // Partial result storage
    logic signed [`OUT_WIDTH-1:0] finF, finB, finResult, finF_delay, finB_delay, partMemB, partMemF;
    logic[$clog2(2*DownResultDepth)-1:0] addrResIn, addrResOutB, addrResOutF, addrResIn_temp, addrResOutB_temp, addrResOutF_temp;
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
    logic signed[`OUT_WIDTH-1:0] scaledResB, scaledResF[6];
    FixToFix #(.n_int_in(n_int), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) ResultScalerB (.in( partResB[N-1] ), .out( scaledResB ) );
    FixToFix #(.n_int_in(n_int), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) ResultScalerF (.in( partResF[N-1] ), .out( scaledResF[0] ) );

    always @(negedge clkDS) begin
        addrResIn_temp = {delayBatCount[2 + Recursion_Delay], delayCycle[2 + Recursion_Delay][0]};
        addrResOutB_temp = {delayBatCountRev[2 + Recursion_Delay], !delayCycle[2 + Recursion_Delay][0]};
        addrResOutF_temp = {delayBatCount[3 + Recursion_Delay], !delayCycle[3 + Recursion_Delay][0]};
    end

    always @(posedge clkDS) begin
        partMemB = scaledResB;
        partMemF = scaledResF[0];
        scaledResF[5] = scaledResF[4];
        scaledResF[4] = scaledResF[3];
        scaledResF[3] = scaledResF[2];
        scaledResF[2] = scaledResF[1];
        scaledResF[1] = scaledResF[0];
        addrResIn = addrResIn_temp;
        addrResOutB = addrResOutB_temp;
        addrResOutF = addrResOutF_temp;
        finF = finF_delay;
        finB = finB_delay;
    end

    always @(negedge clkRecurse) begin
        addrIn_t[2] = addrIn_t[1];
        addrLH_t[2] = addrLH_t[1];
        addrBR_t[2] = addrBR_t[1];
        addrFR_t[2] = addrFR_t[1];
        addrIn_t[1] = addrIn_t[0];
        addrLH_t[1] = addrLH_t[0];
        addrBR_t[1] = addrBR_t[0];
        addrFR_t[1] = addrFR_t[0];
        addrIn_t[0] = {dBatCount, cycle};
        addrLH_t[0] = {dBatCountRev, cycleLH};
        addrBR_t[0] = {dBatCountRev, cycleCalc};
        addrFR_t[0] = {dBatCount, cycleCalc};
    end

    always @(posedge clkRecurse) begin
        //scof = sf_delay;
        addrIn = addrIn_t[0];
        addrLH = addrLH_t[0];
        addrBR = addrBR_t[0];
        addrFR = addrFR_t[0];
    end

    // Must reverse sample order for backward recursion LUTs
    wire[SampleWidth-1:0] slh_rev, scob_rev;
    generate
        for (genvar j = 0; j < OSR1; j++ ) begin
            assign slh_rev[N*j +: N] = slh[N*(OSR1-j-1) +: N];
            assign scob_rev[N*j +: N] = scob[N*(OSR1-j-1) +: N];
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
                .sel(slh_rev), .clk(clkRecurse), .result(LH_inR)
                );

            FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFfr), .n_int(n_int), .n_mant(n_mant)) CF_LUTr (
                .sel(scof), .clk(clkRecurse), .result(CF_inR)
                );

            FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFbr), .n_int(n_int), .n_mant(n_mant)) CB_LUTr (
                .sel(scob_rev), .clk(clkRecurse), .result(CB_inR)
            );

            FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFbi), .n_int(n_int), .n_mant(n_mant)) LH_LUTi (
                .sel(slh_rev), .clk(clkRecurse), .result(LH_inI)
                );

            FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFfi), .n_int(n_int), .n_mant(n_mant)) CF_LUTi (
                .sel(scof), .clk(clkRecurse), .result(CF_inI)
                );

            FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFbi), .n_int(n_int), .n_mant(n_mant)) CB_LUTi (
                .sel(scob_rev), .clk(clkRecurse), .result(CB_inI)
            );

            localparam logic signed[1:0][n_tot:0] tempLb = cpow_fixed(Lbr[i], Lbi[i], OSR1);
            localparam logic signed[1:0][n_tot:0] tempLf = cpow_fixed(Lfr[i], Lfi[i], OSR1);

            logic signed[n_tot:0] LH_resR, LH_resI, CF_outR, CF_outI, CB_outR, CB_outI, WFR, WFI, WBR, WBI;
            // Lookahead 
            FixRecursionModule #(.factorR(tempLb[0]), .factorI(tempLb[1]), .n_int(n_int), .n_mant(n_mant)) LHR_ (
                .inR(LH_inR), .inI(LH_inI), .rst(regProp[LUT_Delay] & rst), .resetValR(0), .resetValI(0), .clk(clkRecurse), .outR(LH_resR), .outI(LH_resI)
                );
            // Compute
            logic signed[n_tot:0] RF_inR, RF_inI, RB_inR, RB_inI;
            assign RF_inR = validCompute ? CF_inR : 0;
            assign RB_inR = validCompute ? CB_inR : 0;
            assign RF_inI = validCompute ? CF_inI : 0;
            assign RB_inI = validCompute ? CB_inI : 0;
            FixRecursionModule #(.factorR(tempLf[0]), .factorI(tempLf[1]), .n_int(n_int), .n_mant(n_mant)) CFR_ (
                .inR(RF_inR), .inI(RF_inI), .rst(rst), .resetValR(0), .resetValI(0), .clk(clkRecurse), .outR(CF_outR), .outI(CF_outI)
                );
            FixRecursionModule #(.factorR(tempLb[0]), .factorI(tempLb[1]), .n_int(n_int), .n_mant(n_mant)) CBR_ (
                .inR(RB_inR), .inI(RB_inI), .rst(regProp[LUT_Delay] & rst), .resetValR(LH_resR), .resetValI(LH_resI), .clk(clkRecurse), .outR(CB_outR), .outI(CB_outI)
                );
            
            assign WFR = Wfr[i] >>> (COEFF_BIAS - n_mant);
            assign WFI = Wfi[i] >>> (COEFF_BIAS - n_mant);
            assign WBR = Wbr[i] >>> (COEFF_BIAS - n_mant);
            assign WBI = Wbi[i] >>> (COEFF_BIAS - n_mant);

            // Sync between different clocks
            logic signed[n_tot:0] SF_outR, SF_outI, SB_outR, SB_outI;
            always @(posedge clkRecurse) begin
                SF_outR = CF_outR;
                SF_outI = CF_outI;
                SB_outR = CB_outR;
                SB_outI = CB_outI;
            end

            // Save in registers to reduce timing requirements
            logic signed[n_tot:0] F_outR, F_outI, B_outR, B_outI;
            always @(posedge clkDS) begin
                F_outR = CF_outR;
                F_outI = CF_outI;
                B_outR = CB_outR;
                B_outI = CB_outI;
            end

            logic signed[n_tot:0] resFR, resFI, resBR, resBI;
            CFixPU #(.op(FPU_p::MULT), .n_int(n_int), .n_mant(n_mant)) WFR_ (.AR(F_outR), .AI(F_outI), .BR(WFR), .BI(WFI), .clk(clkDS), .resultR(resFR), .resultI(resFI));
            CFixPU #(.op(FPU_p::MULT), .n_int(n_int), .n_mant(n_mant)) WBR_ (.AR(B_outR), .AI(B_outI), .BR(WBR), .BI(WBI), .clk(clkDS), .resultR(resBR), .resultI(resBI));



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
                FixPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) FINADDF (.A(partResF[i-1]), .B(forward), .clk(clkDS), .result(partResF[i]));
                FixPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) FINADDB (.A(partResB[i-1]), .B(backward), .clk(clkDS), .result(partResB[i]));
            end
        end
    endgenerate

    // Final final result
    FixPU #(.op(FPU_p::ADD), .n_int(0), .n_mant(`OUT_WIDTH-1)) FINADD (.A(finF), .B(finB), .clk(clkDS), .result(finResult));
    always @(posedge clkDS) begin
        out = {!finResult[`OUT_WIDTH-1], finResult[`OUT_WIDTH-2:0]};
    end
endmodule

`endif