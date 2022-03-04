`ifndef BATCH_FLP_SV_
`define BATCH_FLP_SV_

/*
`ifndef EXP_W
    `define EXP_W 6
`endif  // EXP_W
`ifndef MANT_W
    `define MANT_W 12
`endif  // MANT_W
*/
`include "Util.sv"
`include "FPU.sv"
`include "CFPU.sv"
`include "Recursion_Flp.sv"
`include "LUT_Flp.sv"
`include "Flp_To_Fxp.sv"
`include "ClkDiv.sv"
`include "ValidCount.sv"
`include "InputReg.sv"
`include "Delay.sv"

`define MAX_LUT_SIZE 7
`define COMB_ADDERS 1
`define OUT_WIDTH 14

module Batch_Flp #(
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
    import Coefficients_Fx::N;
    import Coefficients_Fx::M;
    
    import Coefficients_Fx::COEFF_BIAS;
    localparam int DownSampleDepth = $ceil((0.0 + depth) / DSR);
    localparam SampleWidth = M*DSR;
    localparam int LUT_Layers = $clog2(int'($ceil((0.0 + SampleWidth)/`MAX_LUT_SIZE)));
    localparam int LUT_Delay = $floor((0.0 + LUT_Layers)/`COMB_ADDERS) + 1;

    input wire [M-1:0] in;
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
    // Backward result
    assign resClkB = clkDS;
    assign resWriteB = 1'b1;
    assign resDataInB = partMemB;
    assign resAddrInB = addrResIn;
    assign finB_delay = resDataOutB;
    assign resAddrOutB = addrResOutB;
    // Forward result
    assign resClkF = clkDS;
    assign resWriteF = 1'b1;
    assign resDataInF = partMemF;
    assign resAddrInF = addrResIn;
    assign finF_delay = resDataOutF;
    assign resAddrOutF = addrResOutF;

    // Outputs from generate blocks
    float_t forwardResult, backwardResult;

    // Scale results
    logic signed[`OUT_WIDTH-1:0] scaledResB, scaledResF;
    Flp_To_Fxp #(.n_exp_in(n_exp), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1), .float_t(float_t)) ResultScalerB (.in( backwardResult ), .out( scaledResB ) );
    Flp_To_Fxp #(.n_exp_in(n_exp), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1), .float_t(float_t)) ResultScalerF (.in( forwardResult ), .out( scaledResF ) );

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

    // Must reverse sample order for backward recursion LUTs
    logic[SampleWidth-1:0] slh_rev, scob_rev;
    generate
        genvar j;
        for (j = 0; j < DSR; j++ ) begin
            assign slh_rev[M*j +: M] = slh[M*(DSR-j-1) +: M];
            assign scob_rev[M*j +: M] = scob[M*(DSR-j-1) +: M];
        end
    endgenerate

    // Generate recursions
    float_t partResB[N], partResF[N];
    generate 
        genvar i;
        for (i = 0; i < N ; i++ ) begin
            
            // Import constants
            GetRecConst #(.n_int(63-COEFF_BIAS), .n_mant(COEFF_BIAS), .size(SampleWidth), .row(i), .dsr(DSR)) loop_const ();
            localparam float_t FloatZero = 0;
            
            // Use LUTs to turn sample into a complex number
            complex_t CF_in, CB_in, LH_in;
            LUT_Unit_Flp #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(loop_const.Fbr), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t)) LH_LUTr (
                .sel(slh_rev), .clk(clkDS), .result(LH_in.r)
                );

            LUT_Unit_Flp #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(loop_const.Ffr), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t)) CF_LUTr (
                .sel(scof), .clk(clkDS), .result(CF_in.r)
                );

            LUT_Unit_Flp #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(loop_const.Fbr), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t)) CB_LUTr (
                .sel(scob_rev), .clk(clkDS), .result(CB_in.r)
            );

            LUT_Unit_Flp #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(loop_const.Fbi), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t)) LH_LUTi (
                .sel(slh_rev), .clk(clkDS), .result(LH_in.i)
                );

            LUT_Unit_Flp #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(loop_const.Ffi), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t)) CF_LUTi (
                .sel(scof), .clk(clkDS), .result(CF_in.i)
                );

            LUT_Unit_Flp #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(loop_const.Fbi), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t)) CB_LUTi (
                .sel(scob_rev), .clk(clkDS), .result(CB_in.i)
            );


            // Calculate Lookahead
            complex_t LH_res;
            Recursion_Flp #(
                .factorR(loop_const.Lb[0]), .factorI(loop_const.Lb[1]), .n_int(63-COEFF_BIAS), .n_mant(COEFF_BIAS), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t), .complex_t(complex_t)) LHR_ (
                .in(LH_in), .rst(regProp & rst), .resetVal({FloatZero, FloatZero}), .clk(clkDS || !rst), .out(LH_res));
            
            // Calculate forward result
            complex_t CF_out, RF_in;
            assign RF_in = validCompute ? CF_in : {FloatZero, FloatZero};
            Recursion_Flp #(
                .factorR(loop_const.Lf[0]), .factorI(loop_const.Lf[1]), .n_int(63-COEFF_BIAS), .n_mant(COEFF_BIAS), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t), .complex_t(complex_t)) CFR_ (
                .in(RF_in), .rst(rst), .resetVal({FloatZero, FloatZero}), .clk(clkDS || !rst), .out(CF_out));
            
            // Calculate backward result
            complex_t CB_out, RB_in;
            assign RB_in = validCompute ? CB_in : {FloatZero, FloatZero};
            Recursion_Flp #(
                .factorR(loop_const.Lb[0]), .factorI(loop_const.Lb[1]), .n_int(63-COEFF_BIAS), .n_mant(COEFF_BIAS), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t), .complex_t(complex_t)) CBR_ (
                .in(RB_in), .rst(regProp & rst), .resetVal(LH_res), .clk(clkDS || !rst), .out(CB_out));
            
            // Save in registers to reduce timing requirements
            complex_t F_out, B_out;
            always @(posedge clkDS) begin
                F_out <= CF_out;
                B_out <= CB_out;
            end

            // Prepare factors W
            complex_t WF, WB;
            ConvertITOF #(.n_int(63-COEFF_BIAS), .n_mant(COEFF_BIAS), .f_exp(n_exp), .f_mant(n_mant), .in(Coefficients_Fx::Wfr[i])) itofWFR ();
            ConvertITOF #(.n_int(63-COEFF_BIAS), .n_mant(COEFF_BIAS), .f_exp(n_exp), .f_mant(n_mant), .in(Coefficients_Fx::Wfi[i])) itofWFI ();
            ConvertITOF #(.n_int(63-COEFF_BIAS), .n_mant(COEFF_BIAS), .f_exp(n_exp), .f_mant(n_mant), .in(Coefficients_Fx::Wbr[i])) itofWBR ();
            ConvertITOF #(.n_int(63-COEFF_BIAS), .n_mant(COEFF_BIAS), .f_exp(n_exp), .f_mant(n_mant), .in(Coefficients_Fx::Wbi[i])) itofWBI ();
            assign WF.r = itofWFR.result;
            assign WF.i = itofWFI.result;
            assign WB.r = itofWBR.result;
            assign WB.i = itofWBI.result;

            // Multiply by W
            complex_t resF, resB;
            CFPU #(.op(FPU_p::MULT), .n_exp(n_exp), .n_mant(n_mant), .float_t(float_t), .complex_t(complex_t)) WFR_ (.A(F_out), .B(WF), .clk(clkDS), .result(resF));
            CFPU #(.op(FPU_p::MULT), .n_exp(n_exp), .n_mant(n_mant), .float_t(float_t), .complex_t(complex_t)) WBR_ (.A(B_out), .B(WB), .clk(clkDS), .result(resB));

            // Assign to array
            always @(posedge clkDS) begin
                partResF[i] <= resF.r;
                partResB[i] <= resB.r;
            end
        end
    endgenerate

    // Sum forward partial results
    Sum_Flp #(.size(N), .f_exp(n_exp), .f_mant(n_mant), .adders_comb(N), .float_t(float_t)) sumF (.in(partResF), .clk(clkDS), .out(forwardResult));

    // Sum backward partial results
    Sum_Flp #(.size(N), .f_exp(n_exp), .f_mant(n_mant), .adders_comb(N), .float_t(float_t)) sumB (.in(partResB), .clk(clkDS), .out(backwardResult));

    // Final final result
    assign finResult = finF + finB; // FPU #(.op(FPU_p::ADD), .n_exp(n_exp), .n_mant(n_mant), .float_t(float_t)) FINADD (.A(finF), .B(finB), .clk(clkDS), .result(finResult));
    always @(posedge clkDS) begin
        out <= {!finResult[`OUT_WIDTH-1], finResult[`OUT_WIDTH-2:0]};
    end
endmodule

`endif