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
    import Coefficients::*;
    localparam DownSampleDepth = $rtoi($ceil(depth / OSR));
    localparam SampleWidth = N*OSR; 
    localparam LUTsplit = $rtoi($ceil(N*OSR/`MAX_LUT_SIZE +1));
    localparam n_tot = n_int + n_mant;
    localparam LUT_Delay = $clog2($rtoi($ceil((0.0 + SampleWidth)/`MAX_LUT_SIZE))) + 1;

    input wire [N-1:0] in;
    input logic rst, clk;
    output logic[`OUT_WIDTH-1:0] out;
    output logic valid;
    // Sample memory
    output logic[$clog2(4*$rtoi($ceil(depth / OSR)))-1:0]  sampleAddrIn, sampleAddrOut1, sampleAddrOut2, sampleAddrOut3;
	output logic sampleClk, sampleWrite;
	output logic[N*OSR-1:0] sampleDataIn;
	input logic[N*OSR-1:0] sampleDataOut1, sampleDataOut2, sampleDataOut3;
    // Part result memory
    output logic[$clog2(2*$rtoi($ceil(depth / OSR)))-1:0]  resAddrInF, resAddrInB, resAddrOutF, resAddrOutB;
	output logic resClkF, resClkB, resWriteF, resWriteB;
	output logic[`OUT_WIDTH-1:0] resDataInF, resDataInB;
	input logic[`OUT_WIDTH-1:0] resDataOutF, resDataOutB;

    // Downsampled clock
    logic[$clog2(OSR)-1:0] osrCount = 0;      // Prescale counter
    logic clkDS, rstPrev;
    generate
        if(OSR > 1) begin
            always @(posedge clk) begin
                if(!rst && rstPrev) begin
                    osrCount = 0;
                end else
                    osrCount++;
                if (osrCount >= OSR) begin
                    osrCount = 0;
                end
                rstPrev = rst;
            end
            assign clkDS = (osrCount <= $rtoi($floor(OSR/2)));
        end else begin
            assign clkDS = clk;
        end
    endgenerate

    // Shifted input
    logic[SampleWidth-1:0] inShift, inShiftTemp;

    // Generates shift register if OSR > 1
    generate
        if (OSR > 1) begin
            always @(posedge clk) begin
                inShiftTemp[SampleWidth-1:N] = inShiftTemp[SampleWidth-N-1:0];
                inShiftTemp[N-1:0] = in;
            end

            always @(posedge clkDS) begin
                inShift = inShiftTemp;
            end
        end else begin
            always @(posedge clk) begin
                inShift = in;
            end
        end
    endgenerate

    // Counters for batch cycle
    logic[$clog2(DownSampleDepth)-1:0] dBatCount, dBatCountRev;     // counters for input samples
    logic[$clog2(DownSampleDepth)-1:0] delayBatCount[2:0], delayBatCountRev[2:0];
    always @(posedge clkDS) begin
        delayBatCount[2] = delayBatCount[1];
        delayBatCount[1] = delayBatCount[0];
        delayBatCount[0] = dBatCount;
        delayBatCountRev[2] = delayBatCountRev[1];
        delayBatCountRev[1] = delayBatCountRev[0];
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
    localparam ValidDelay = 4*DownSampleDepth + 2;
    logic[$clog2(ValidDelay):0] validCount;
    logic validResult, validCompute;
    always @(posedge clkDS) begin
        if(!rst)
            validCount = 'b0;
        else if (!validResult) begin
            validCount++;
        end   
    end

    assign validResult = validCount == ValidDelay;
    assign validCompute = validCount > 3*DownSampleDepth;
    assign valid = validResult;

    // Is low when the cycle is ending
    logic cyclePulse;
    assign cyclePulse = !(dBatCount == (DownSampleDepth-1));

    // Recursion register propagation is delayed one half cycle
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
        addrResIn = {delayBatCount[2], delayCycle[2][0]};
        addrResOutB = {delayBatCountRev[1], !delayCycle[1][0]};
        addrResOutF = {delayBatCount[1], !delayCycle[1][0]};
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

    function automatic logic signed[SampleWidth-1:0][n_tot:0] GetFbr (int row, int startIndex);
        logic signed[SampleWidth-1:0][n_tot:0] tempArray;
        for (int i = 0; i < SampleWidth ; i++) begin
            tempArray[i][n_tot:0] = Fbr[row][startIndex + i] >>> (COEFF_BIAS - n_mant);
        end
        return tempArray;
    endfunction

    function automatic logic signed[SampleWidth-1:0][n_tot:0] GetFbi (int row, int startIndex);
        logic signed[SampleWidth-1:0][n_tot:0] tempArray;
        for (int i = 0; i < SampleWidth ; i++) begin
            tempArray[i][n_tot:0] = Fbi[row][startIndex + i] >>> (COEFF_BIAS - n_mant);
        end
        return tempArray;
    endfunction

    function automatic logic signed[SampleWidth-1:0][n_tot:0] GetFfr (int row, int startIndex);
        logic signed[SampleWidth-1:0][n_tot:0] tempArray;
        for (int i = 0; i < SampleWidth ; i++) begin
            tempArray[i][n_tot:0] = Ffr[row][startIndex + i] >>> (COEFF_BIAS - n_mant);
        end
        return tempArray;
    endfunction

    function automatic logic signed[SampleWidth-1:0][n_tot:0] GetFfi (int row, int startIndex);
        logic signed[SampleWidth-1:0][n_tot:0] tempArray;
        for (int i = 0; i < SampleWidth ; i++) begin
            tempArray[i][n_tot:0] = Ffi[row][startIndex + i] >>> (COEFF_BIAS - n_mant);
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
            
            localparam logic signed[SampleWidth-1:0][n_tot:0] tempFfr = GetFfr(i, 0);
            localparam logic signed[SampleWidth-1:0][n_tot:0] tempFbr = GetFbr(i, 0);
            localparam logic signed[SampleWidth-1:0][n_tot:0] tempFfi = GetFfi(i, 0);
            localparam logic signed[SampleWidth-1:0][n_tot:0] tempFbi = GetFbi(i, 0);

            FixLUT_Unit #(
                .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFbr), .n_int(n_int), .n_mant(n_mant)) LH_LUTr (
                .sel(slh_rev), .clk(clkDS), .result(LH_inR)
                );

            FixLUT_Unit #(
                .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFfr), .n_int(n_int), .n_mant(n_mant)) CF_LUTr (
                .sel(scof), .clk(clkDS), .result(CF_inR)
                );

            FixLUT_Unit #(
                .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFbr), .n_int(n_int), .n_mant(n_mant)) CB_LUTr (
                .sel(scob_rev), .clk(clkDS), .result(CB_inR)
            );

            FixLUT_Unit #(
                .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFbi), .n_int(n_int), .n_mant(n_mant)) LH_LUTi (
                .sel(slh_rev), .clk(clkDS), .result(LH_inI)
                );

            FixLUT_Unit #(
                .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFfi), .n_int(n_int), .n_mant(n_mant)) CF_LUTi (
                .sel(scof), .clk(clkDS), .result(CF_inI)
                );

            FixLUT_Unit #(
                .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFbi), .n_int(n_int), .n_mant(n_mant)) CB_LUTi (
                .sel(scob_rev), .clk(clkDS), .result(CB_inI)
            );

            /*
            // Split large LUTs
            if (LUTsplit == 0) begin
                $error("Can't generate 0 LUTs");
            end
            //if (LUTsplit > 1) begin
                logic signed[n_tot:0] LH_in_partR[LUTsplit-1:0];
                logic signed[n_tot:0] LH_in_partI[LUTsplit-1:0];
                logic signed[n_tot:0] CF_in_partR[LUTsplit-1:0];
                logic signed[n_tot:0] CF_in_partI[LUTsplit-1:0];
                logic signed[n_tot:0] CB_in_partI[LUTsplit-1:0];
                logic signed[n_tot:0] CB_in_partR[LUTsplit-1:0];

                genvar lut_i;
                for (lut_i = 0; lut_i < LUTsplit ; lut_i++ ) begin
                    localparam lut_offset = `MAX_LUT_SIZE*lut_i;
                    localparam lut_rem = SampleWidth - lut_offset;
                    localparam logic signed[`MAX_LUT_SIZE-1:0][n_tot:0] tempFfr = GetFfr(i, lut_offset);
                    localparam logic signed[`MAX_LUT_SIZE-1:0][n_tot:0] tempFbr = GetFbr(i, lut_offset);
                    localparam logic signed[`MAX_LUT_SIZE-1:0][n_tot:0] tempFfi = GetFfi(i, lut_offset);
                    localparam logic signed[`MAX_LUT_SIZE-1:0][n_tot:0] tempFbi = GetFbi(i, lut_offset);
                    logic signed[n_tot:0] tempLHR, tempLHI, tempCFR, tempCFI, tempCBR, tempCBI;
                    if (lut_rem >= `MAX_LUT_SIZE) begin
                        // Lookahead
                        FixLUT #(.size(`MAX_LUT_SIZE), .fact(tempFbr), .n_int(n_int), .n_mant(n_mant)) LHLR_ (.sel(slh_rev[lut_offset +: `MAX_LUT_SIZE]), .result(tempLHR));
                        FixLUT #(.size(`MAX_LUT_SIZE), .fact(tempFbi), .n_int(n_int), .n_mant(n_mant)) LHLI_ (.sel(slh_rev[lut_offset +: `MAX_LUT_SIZE]), .result(tempLHI));
                        // Compute
                        FixLUT #(.size(`MAX_LUT_SIZE), .fact(tempFfr), .n_int(n_int), .n_mant(n_mant)) CFLR_ (.sel(scof[lut_offset +: `MAX_LUT_SIZE]), .result(tempCFR));
                        FixLUT #(.size(`MAX_LUT_SIZE), .fact(tempFfi), .n_int(n_int), .n_mant(n_mant)) CFLI_ (.sel(scof[lut_offset +: `MAX_LUT_SIZE]), .result(tempCFI));
                        FixLUT #(.size(`MAX_LUT_SIZE), .fact(tempFbr), .n_int(n_int), .n_mant(n_mant)) CBLR_ (.sel(scob_rev[lut_offset +: `MAX_LUT_SIZE]), .result(tempCBR));
                        FixLUT #(.size(`MAX_LUT_SIZE), .fact(tempFbi), .n_int(n_int), .n_mant(n_mant)) CBLI_ (.sel(scob_rev[lut_offset +: `MAX_LUT_SIZE]), .result(tempCBI));
                    end else if(lut_rem > 0) begin
                        // Lookahead
                        FixLUT #(.size(lut_rem), .fact(tempFbr[lut_rem-1:0]), .n_int(n_int), .n_mant(n_mant)) LHLR_ (.sel(slh_rev[lut_offset +: lut_rem]), .result(tempLHR));
                        FixLUT #(.size(lut_rem), .fact(tempFbi[lut_rem-1:0]), .n_int(n_int), .n_mant(n_mant)) LHLI_ (.sel(slh_rev[lut_offset +: lut_rem]), .result(tempLHI));
                        // Compute
                        FixLUT #(.size(lut_rem), .fact(tempFfr[lut_rem-1:0]), .n_int(n_int), .n_mant(n_mant)) CFLR_ (.sel(scof[lut_offset +: lut_rem]), .result(tempCFR));
                        FixLUT #(.size(lut_rem), .fact(tempFfi[lut_rem-1:0]), .n_int(n_int), .n_mant(n_mant)) CFLI_ (.sel(scof[lut_offset +: lut_rem]), .result(tempCFI));
                        FixLUT #(.size(lut_rem), .fact(tempFbr[lut_rem-1:0]), .n_int(n_int), .n_mant(n_mant)) CBLR_ (.sel(scob_rev[lut_offset +: lut_rem]), .result(tempCBR));
                        FixLUT #(.size(lut_rem), .fact(tempFbi[lut_rem-1:0]), .n_int(n_int), .n_mant(n_mant)) CBLI_ (.sel(scob_rev[lut_offset +: lut_rem]), .result(tempCBI));
                    end else begin
                        $error("Faulty LUT generation! LUT rest = %d", lut_rem);
                    end

                    // Sum results
                    if (lut_i == 0) begin
                        assign LH_in_partR[0] = tempLHR;
                        assign CF_in_partR[0] = tempCFR;
                        assign CB_in_partR[0] = tempCBR;
                        assign LH_in_partI[0] = tempLHI;
                        assign CF_in_partI[0] = tempCFI;
                        assign CB_in_partI[0] = tempCBI;
                    end else begin
                        CFixPU #(.op(ADD), .n_int(n_int), .n_mant(n_mant)) LLH_ (.AR(LH_in_partR[lut_i-1]), .AI(LH_in_partI[lut_i-1]), .BR(tempLHR), .BI(tempLHI), .clk(clkDS), .resultR(LH_in_partR[lut_i]), .resultI(LH_in_partI[lut_i]));
                        CFixPU #(.op(ADD), .n_int(n_int), .n_mant(n_mant)) LCF_ (.AR(CF_in_partR[lut_i-1]), .AI(CF_in_partI[lut_i-1]), .BR(tempCFR), .BI(tempCFI), .clk(clkDS), .resultR(CF_in_partR[lut_i]), .resultI(CF_in_partI[lut_i]));
                        CFixPU #(.op(ADD), .n_int(n_int), .n_mant(n_mant)) LCB_ (.AR(CB_in_partR[lut_i-1]), .AI(CB_in_partI[lut_i-1]), .BR(tempCBR), .BI(tempCBI), .clk(clkDS), .resultR(CB_in_partR[lut_i]), .resultI(CB_in_partI[lut_i]));
                    end
                end

                assign LH_inR = LH_in_partR[LUTsplit-1];
                assign CF_inR = CF_in_partR[LUTsplit-1];
                assign CB_inR = CB_in_partR[LUTsplit-1];
                assign LH_inI = LH_in_partI[LUTsplit-1];
                assign CF_inI = CF_in_partI[LUTsplit-1];
                assign CB_inI = CB_in_partI[LUTsplit-1];
            /*end else begin
                localparam logic[n_tot:0] testFbi = GetFbi(i, 0);
                localparam logic[n_tot:0] testFfr = GetFfr(i, 0);
                localparam logic[n_tot:0] testFbr = GetFbr(i, 0);
                localparam logic[n_tot:0] testFfi = GetFfi(i, 0);
                // Lookahead
                FixLUT #(.size(SampleWidth), .fact(testFbr[0:SampleWidth-1]), .n_int(n_int), .n_mant(n_mant)) LHLR_ (.sel(slh_rev), .result(LH_in.r));
                FixLUT #(.size(SampleWidth), .fact(testFbi[0:SampleWidth-1]), .n_int(n_int), .n_mant(n_mant)) LHLI_ (.sel(slh_rev), .result(LH_in.i));
                // Compute
                FixLUT #(.size(SampleWidth), .fact(testFfr[0:SampleWidth-1]), .n_int(n_int), .n_mant(n_mant)) CFLR_ (.sel(scof), .result(CF_in.r));
                FixLUT #(.size(SampleWidth), .fact(testFfi[0:SampleWidth-1]), .n_int(n_int), .n_mant(n_mant)) CFLI_ (.sel(scof), .result(CF_in.i));
                FixLUT #(.size(SampleWidth), .fact(testFbr[0:SampleWidth-1]), .n_int(n_int), .n_mant(n_mant)) CBLR_ (.sel(scob_rev), .result(CB_in.r));
                FixLUT #(.size(SampleWidth), .fact(testFbi[0:SampleWidth-1]), .n_int(n_int), .n_mant(n_mant)) CBLI_ (.sel(scob_rev), .result(CB_in.i));
            end*/

            localparam logic signed[1:0][n_tot:0] tempLb = cpow_fixed(Lbr[i], Lbi[i], OSR);
            localparam logic signed[1:0][n_tot:0] tempLf = cpow_fixed(Lfr[i], Lfi[i], OSR);
            localparam logic[n_tot:0] R_VAL = 0;

            logic signed[n_tot:0] LH_resR, LH_resI, CF_outR, CF_outI, CB_outR, CB_outI, WFR, WFI, WBR, WBI;
            // Lookahead 
            FixRecursionModule #(.factorR(tempLb[0][n_tot:0]), .factorI(tempLb[1][n_tot:0]), .n_int(n_int), .n_mant(n_mant)) LHR_ (
                .inR(LH_inR), .inI(LH_inI), .rst(regProp & rst), .resetValR(R_VAL), .resetValI(R_VAL), .clk(clkDS), .outR(LH_resR), .outI(LH_resI)
                );
            // Compute
            logic signed[n_tot:0] RF_inR, RF_inI, RB_inR, RB_inI;
            assign RF_inR = validCompute ? CF_inR : 0;
            assign RB_inR = validCompute ? CB_inR : 0;
            assign RF_inI = validCompute ? CF_inI : 0;
            assign RB_inI = validCompute ? CB_inI : 0;
            FixRecursionModule #(.factorR(tempLf[0][n_tot:0]), .factorI(tempLf[1][n_tot:0]), .n_int(n_int), .n_mant(n_mant)) CFR_ (
                .inR(CF_inR), .inI(CF_inI), .rst(rst), .resetValR(R_VAL), .resetValI(R_VAL), .clk(clkDS), .outR(CF_outR), .outI(CF_outI)
                );
            FixRecursionModule #(.factorR(tempLb[0][n_tot:0]), .factorI(tempLb[1][n_tot:0]), .n_int(n_int), .n_mant(n_mant)) CBR_ (
                .inR(CB_inR), .inI(CB_inI), .rst(regProp & rst), .resetValR(LH_resR), .resetValI(LH_resI), .clk(clkDS), .outR(CB_outR), .outI(CB_outI)
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