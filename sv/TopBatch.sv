`ifndef TOPBATCH_SV_
`define TOPBATCH_SV_

`ifndef EXP_W
    `define EXP_W 6
`endif  // EXP_W
`ifndef MANT_W
    `define MANT_W 12
`endif  // MANT_W

`include "Util.sv"
`include "Data/Coefficients_Fixedpoint.sv"
`include "FPU.sv"
`include "CFPU.sv"
`include "RecursionModule.sv"
`include "LUT.sv"
`include "FloatToFix.sv"

//import Float_p::convert;

`define MAX_LUT_SIZE 7
`define COMB_ADDERS 1
`define OUT_WIDTH 14

module Batch_top #(
    parameter depth = 228,
    parameter DSR = 12,
                n_exp = 8,
                n_mant = 23
) (
    in, rst, clk, out, valid,
    // Sample memory
    sampleAddrIn, sampleAddrOut1, sampleAddrOut2, sampleAddrOut3,
	sampleClk, sampleWrite,
	sampleDataIn,
	sampleDataOut1, sampleDataOut2, sampleDataOut3,
    // Part result memory
    resAddrInF, resAddrInB, resAddrOutF, resAddrOutB,
	resClkF, resClkB, resWriteF, resWriteB,
	resDataInF, resDataInB,
	resDataOutF, resDataOutB
);
    import Coefficients_Fx::*;

    localparam int DownSampleDepth = $ceil((0.0 + depth) / DSR);
    localparam SampleWidth = N*DSR;
    localparam int LUT_Layers = $clog2(int'($ceil((0.0 + SampleWidth)/`MAX_LUT_SIZE)));
    localparam int LUT_Delay = $ceil((0.0 + LUT_Layers)/`COMB_ADDERS);

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
    output logic[$clog2(2*DownSampleDepth)-1:0]  resAddrInF, resAddrInB, resAddrOutF, resAddrOutB;
	output logic resClkF, resClkB, resWriteF, resWriteB;
	output logic[`OUT_WIDTH-1:0] resDataInF, resDataInB;
	input logic[`OUT_WIDTH-1:0] resDataOutF, resDataOutB;

    typedef struct packed { 
        logic sign; 
        logic[n_exp-1:0] exp;
        logic[n_mant-1:0] mant;
    } float_t;
        
    typedef struct packed {
        float_t r;
        float_t i;
    } complex_t;


    // Downsampled clock
    logic[$clog2(DSR)-1:0] dsrCount;      // Prescale counter
    logic clkDS;
    generate
        if(DSR > 1) begin
            always @(posedge clk) begin
                if ((!rst) || (dsrCount == (DSR-1)))
                    dsrCount[$clog2(DSR)-1:0] = 'b0;
                else
                    dsrCount++;

                if (dsrCount == 0)
                    clkDS = 1;
                if (dsrCount == DSR/2)
                    clkDS = 0;
                
            end
        end else begin
            assign clkDS = clk;
        end
    endgenerate 

    // Shifted input
    logic[SampleWidth-1:0] inShift, inSample;
    logic[$clog2(SampleWidth)-1:0] inSel;

    // Generates register if DSR > 1
    generate
        if (DSR > 1) begin
            always @(posedge clk) begin
                inSel = N*(DSR - dsrCount)-1;
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
    localparam validTime = 4*DownSampleDepth + LUT_Delay + 2;
    logic[$clog2(validTime):0] validCount;
    logic validClk, validResult, validCompute;
    always @(posedge validClk, negedge rst) begin
        if(!rst) begin
            validCount = 'b0;
            validCompute = 'b0;
        end else begin
            validCount++;
            validCompute = validCompute | (validCount == (3*DownSampleDepth + LUT_Delay) + 2);
        end
    end

    assign validResult = validCount == validTime;
    assign validClk = clkDS && !validResult;
    assign valid = validResult;

    // Is low when the cycle is ending
    logic cyclePulse;
    assign cyclePulse = !(dBatCount == (DownSampleDepth-1));

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

    // Recursion register propagation is delayed one half cycle
    logic[LUT_Delay:0] regProp;
    always @(negedge clkDS) begin
        regProp = regProp << 1;
        regProp[0] = cyclePulse;
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
    float_t partResF[N], partResB[N];

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
    FloatToFix #(.n_exp_in(n_exp), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1), .float_t(float_t)) ResultScalerB (.in( partResB[N-1] ), .out( scaledResB ) );
    FloatToFix #(.n_exp_in(n_exp), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1), .float_t(float_t)) ResultScalerF (.in( partResF[N-1] ), .out( scaledResF ) );

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
    logic[SampleWidth-1:0] slh_rev, scob_rev;
    generate
        genvar j;
        for (j = 0; j < DSR; j++ ) begin
            assign slh_rev[N*j +: N] = slh[N*(DSR-j-1) +: N];
            assign scob_rev[N*j +: N] = scob[N*(DSR-j-1) +: N];
        end
    endgenerate

    function automatic logic signed[SampleWidth-1:0][63:0] GetFbr (int row);
        logic signed[SampleWidth-1:0][63:0] tempArray;
        for (int i = 0; i < SampleWidth ; i++) begin
            tempArray[i][63:0] = Fbr[row][i];
        end
        return tempArray;
    endfunction

    function automatic logic signed[SampleWidth-1:0][63:0] GetFbi (int row);
        logic signed[SampleWidth-1:0][63:0] tempArray;
        for (int i = 0; i < SampleWidth ; i++) begin
            tempArray[i][63:0] = Fbi[row][i];
        end
        return tempArray;
    endfunction

    function automatic logic signed[SampleWidth-1:0][63:0] GetFfr (int row);
        logic signed[SampleWidth-1:0][63:0] tempArray;
        for (int i = 0; i < SampleWidth ; i++) begin
            tempArray[i][63:0] = Ffr[row][i];
        end
        return tempArray;
    endfunction

    function automatic logic signed[SampleWidth-1:0][63:0] GetFfi (int row);
        logic signed[SampleWidth-1:0][63:0] tempArray;
        for (int i = 0; i < SampleWidth ; i++) begin
            tempArray[i][63:0] = Ffi[row][i];
        end
        return tempArray;
    endfunction

    function automatic logic signed[1:0][63:0] cpow_fixed(logic signed[63:0] r, logic signed[63:0] i, int exp);
        logic signed[1:0][63:0] result;
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
        result[0][63:0] = tempR;
        result[1][63:0] = tempI;
        return result;
    endfunction

    generate 
        genvar i;
        for (i = 0; i < N ; i++ ) begin
            
            complex_t CF_in, CB_in, LH_in;

            localparam logic signed[SampleWidth-1:0][63:0] tempFfr = GetFfr(i);
            localparam logic signed[SampleWidth-1:0][63:0] tempFbr = GetFbr(i);
            localparam logic signed[SampleWidth-1:0][63:0] tempFfi = GetFfi(i);
            localparam logic signed[SampleWidth-1:0][63:0] tempFbi = GetFbi(i);
            
            LUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFbr), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t)) LH_LUTr (
                .sel(slh_rev), .clk(clkDS), .result(LH_in.r)
                );

            LUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFfr), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t)) CF_LUTr (
                .sel(scof), .clk(clkDS), .result(CF_in.r)
                );

            LUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFbr), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t)) CB_LUTr (
                .sel(scob_rev), .clk(clkDS), .result(CB_in.r)
            );

            LUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFbi), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t)) LH_LUTi (
                .sel(slh_rev), .clk(clkDS), .result(LH_in.i)
                );

            LUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFfi), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t)) CF_LUTi (
                .sel(scof), .clk(clkDS), .result(CF_in.i)
                );

            LUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFbi), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t)) CB_LUTi (
                .sel(scob_rev), .clk(clkDS), .result(CB_in.i)
            );

            localparam logic signed[1:0][63:0] tempLb = cpow_fixed(Lbr[i], Lbi[i], DSR);
            localparam logic signed[1:0][63:0] tempLf = cpow_fixed(Lfr[i], Lfi[i], DSR);
            localparam float_t FloatZero = 0; // convert #(.n_int(8), .n_mant(24), .f_exp(n_exp), .f_mant(n_mant))::itof(0);

            complex_t LH_res, CF_out, CB_out, WF, WB;
            // Lookahead 
            RecursionModule #(
                .factorR(tempLb[0]), .factorI(tempLb[1]), .n_int(63-COEFF_BIAS), .n_mant(COEFF_BIAS), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t), .complex_t(complex_t)) LHR_ (
                .in(LH_in), .rst(regProp[LUT_Delay] & rst), .resetVal({FloatZero, FloatZero}), .clk(clkDS), .out(LH_res));
            // Compute
            complex_t RF_in, RB_in;
            assign RF_in = validCompute ? CF_in : {FloatZero, FloatZero};
            assign RB_in = validCompute ? CB_in : {FloatZero, FloatZero};
            RecursionModule #(
                .factorR(tempLf[0]), .factorI(tempLf[1]), .n_int(63-COEFF_BIAS), .n_mant(COEFF_BIAS), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t), .complex_t(complex_t)) CFR_ (
                .in(RF_in), .rst(rst), .resetVal({FloatZero, FloatZero}), .clk(clkDS), .out(CF_out));
            RecursionModule #(
                .factorR(tempLb[0]), .factorI(tempLb[1]), .n_int(63-COEFF_BIAS), .n_mant(COEFF_BIAS), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t), .complex_t(complex_t)) CBR_ (
                .in(RB_in), .rst(regProp[LUT_Delay] & rst), .resetVal(LH_res), .clk(clkDS), .out(CB_out));

            assign WF.r = convert#(.n_int(63-COEFF_BIAS), .n_mant(COEFF_BIAS), .f_exp(n_exp), .f_mant(n_mant))::itof(Wfr[i]);
            assign WF.i = convert#(.n_int(63-COEFF_BIAS), .n_mant(COEFF_BIAS), .f_exp(n_exp), .f_mant(n_mant))::itof(Wfi[i]);
            assign WB.r = convert#(.n_int(63-COEFF_BIAS), .n_mant(COEFF_BIAS), .f_exp(n_exp), .f_mant(n_mant))::itof(Wbr[i]);
            assign WB.i = convert#(.n_int(63-COEFF_BIAS), .n_mant(COEFF_BIAS), .f_exp(n_exp), .f_mant(n_mant))::itof(Wbi[i]);

            // Save in registers to reduce timing requirements
            complex_t F_out, B_out;
            always @(posedge clkDS) begin
                F_out = CF_out;
                B_out = CB_out;
            end

            complex_t resF, resB;
            CFPU #(.op(FPU_p::MULT), .n_exp(n_exp), .n_mant(n_mant), .float_t(float_t), .complex_t(complex_t)) WFR_ (.A(F_out), .B(WF), .clk(clkDS), .result(resF));
            CFPU #(.op(FPU_p::MULT), .n_exp(n_exp), .n_mant(n_mant), .float_t(float_t), .complex_t(complex_t)) WBR_ (.A(B_out), .B(WB), .clk(clkDS), .result(resB));

            // Final add
            float_t forward, backward;
            always @(posedge clkDS) begin
                forward = resF.r;
                backward = resB.r;
            end

            if(i == 0) begin
                assign partResF[0] = forward;
                assign partResB[0] = backward;
            end else begin
                FPU #(.op(FPU_p::ADD), .n_exp(n_exp), .n_mant(n_mant), .float_t(float_t)) FINADDF (.A(partResF[i-1]), .B(forward), .clk(clkDS), .result(partResF[i]));
                FPU #(.op(FPU_p::ADD), .n_exp(n_exp), .n_mant(n_mant), .float_t(float_t)) FINADDB (.A(partResB[i-1]), .B(backward), .clk(clkDS), .result(partResB[i]));
            end
        end
    endgenerate

    // Final final result
    assign finResult = finF + finB; // FPU #(.op(FPU_p::ADD), .n_exp(n_exp), .n_mant(n_mant), .float_t(float_t)) FINADD (.A(finF), .B(finB), .clk(clkDS), .result(finResult));
    always @(posedge clkDS) begin
        out = {!finResult[`OUT_WIDTH-1], finResult[`OUT_WIDTH-2:0]};
    end
endmodule

`endif