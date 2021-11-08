`ifndef TOPBATCH_SV_
`define TOPBATCH_SV_

`ifndef EXP_W
    `define EXP_W 6
`endif  // EXP_W
`ifndef MANT_W
    `define MANT_W 12
`endif  // MANT_W

`include "Util.sv"
`include "Data/Coefficients.sv"
`include "FPU.sv"
`include "CFPU.sv"
`include "RecursionModule.sv"
`include "LUT.sv"

`define MAX_LUT_SIZE 7

module Batch_top #(
    parameter depth = 228,
    parameter OSR = 12
) (
    input wire [Coefficients::N-1:0] in,
    input logic rst, clk,
    output floatType out,
    // Sample memory
    output logic[$clog2(4*$rtoi($ceil(depth / OSR)))-1:0]  sampleAddrIn, sampleAddrOut1, sampleAddrOut2, sampleAddrOut3,
	output logic sampleClk, sampleWrite,
	output logic[Coefficients::N*OSR-1:0] sampleDataIn,
	input logic[Coefficients::N*OSR-1:0] sampleDataOut1, sampleDataOut2, sampleDataOut3,
    // Part result memory
    output logic[$clog2(2*$rtoi($ceil(depth / OSR)))-1:0]  resAddrInF, resAddrInB, resAddrOutF, resAddrOutB,
	output logic resClkF, resClkB, resWriteF, resWriteB,
	output logic[(`EXP_W + `MANT_W):0] resDataInF, resDataInB,
	input logic[(`EXP_W + `MANT_W):0] resDataOutF, resDataOutB
);
    import Coefficients::*;
    localparam DownSampleDepth = $rtoi($ceil(depth / OSR));
    localparam SampleWidth = N*OSR; 
    localparam LUTsplit = $rtoi($ceil(N*OSR/`MAX_LUT_SIZE +1));

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
    logic[$clog2(3*DownSampleDepth):0] validCount;
    logic validCompute;
    always @(posedge clkDS) begin
        if(!rst)
            validCount = 'b0;
        else if (validCount < 3*DownSampleDepth) begin
            validCount++;
        end   
    end

    assign validCompute = validCount == 3*DownSampleDepth;

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
    floatType partResF[N], partResB[N];

    // Partial result storage
    floatType finF, finB, finResult, finF_delay, finB_delay, partMemB, partMemF;
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

    // Must reverse sample order for backward recursion LUTs
    wire[SampleWidth-1:0] slh_rev, scob_rev;
    generate
        genvar j;
        for (j = 0; j < OSR; j++ ) begin
            assign slh_rev[N*j +: N] = slh[N*(OSR-j-1) +: N];
            assign scob_rev[N*j +: N] = scob[N*(OSR-j-1) +: N];
        end
    endgenerate

    function automatic floatType[0:`MAX_LUT_SIZE-1] GetFbr (int row, int startIndex);
        floatType[0:`MAX_LUT_SIZE-1] tempArray;
        for (int i = 0; i < `MAX_LUT_SIZE ; i++) begin
            tempArray[i] = rtof(Fbr[row][startIndex + i]);
        end
        return tempArray;
    endfunction

    function automatic floatType[0:`MAX_LUT_SIZE-1] GetFbi (int row, int startIndex);
        floatType[0:`MAX_LUT_SIZE-1] tempArray;
        for (int i = 0; i < `MAX_LUT_SIZE ; i++) begin
            tempArray[i] = rtof(Fbi[row][startIndex + i]);
        end
        return tempArray;
    endfunction

    function automatic floatType[0:`MAX_LUT_SIZE-1] GetFfr (int row, int startIndex);
        floatType[0:`MAX_LUT_SIZE-1] tempArray;
        for (int i = 0; i < `MAX_LUT_SIZE ; i++) begin
            tempArray[i] = rtof(Ffr[row][startIndex + i]);
        end
        return tempArray;
    endfunction

    function automatic floatType[0:`MAX_LUT_SIZE-1] GetFfi (int row, int startIndex);
        floatType[0:`MAX_LUT_SIZE-1] tempArray;
        for (int i = 0; i < `MAX_LUT_SIZE ; i++) begin
            tempArray[i] = rtof(Ffi[row][startIndex + i]);
        end
        return tempArray;
    endfunction

    generate 
        genvar i;
        for (i = 0; i < N ; i++ ) begin
            // Lookahead
            complex CF_in, CB_in, LH_in;
            // Split large LUTs
            if (LUTsplit == 0) begin
                $error("Can't generate 0 LUTs");
            end
            //if (LUTsplit > 1) begin
                complex LH_in_part[LUTsplit-1:0];
                complex CF_in_part[LUTsplit-1:0];
                complex CB_in_part[LUTsplit-1:0];
                genvar lut_i;
                for (lut_i = 0; lut_i < LUTsplit ; lut_i++ ) begin
                    localparam lut_offset = `MAX_LUT_SIZE*lut_i;
                    localparam lut_rem = SampleWidth - lut_offset;
                    localparam floatType[0:`MAX_LUT_SIZE-1] tempFfr = GetFfr(i, lut_offset);
                    localparam floatType[0:`MAX_LUT_SIZE-1] tempFbr = GetFbr(i, lut_offset);
                    localparam floatType[0:`MAX_LUT_SIZE-1] tempFfi = GetFfi(i, lut_offset);
                    localparam floatType[0:`MAX_LUT_SIZE-1] tempFbi = GetFbi(i, lut_offset);
                    complex tempLH, tempCF, tempCB;
                    if (lut_rem >= `MAX_LUT_SIZE) begin
                        // Lookahead
                        LUT #(.size(`MAX_LUT_SIZE), .fact(tempFbr)) LHLR_ (.sel(slh_rev[lut_offset +: `MAX_LUT_SIZE]), .result(tempLH.r));
                        LUT #(.size(`MAX_LUT_SIZE), .fact(tempFbi)) LHLI_ (.sel(slh_rev[lut_offset +: `MAX_LUT_SIZE]), .result(tempLH.i));
                        // Compute
                        LUT #(.size(`MAX_LUT_SIZE), .fact(tempFfr)) CFLR_ (.sel(scof[lut_offset +: `MAX_LUT_SIZE]), .result(tempCF.r));
                        LUT #(.size(`MAX_LUT_SIZE), .fact(tempFfi)) CFLI_ (.sel(scof[lut_offset +: `MAX_LUT_SIZE]), .result(tempCF.i));
                        LUT #(.size(`MAX_LUT_SIZE), .fact(tempFbr)) CBLR_ (.sel(scob_rev[lut_offset +: `MAX_LUT_SIZE]), .result(tempCB.r));
                        LUT #(.size(`MAX_LUT_SIZE), .fact(tempFbi)) CBLI_ (.sel(scob_rev[lut_offset +: `MAX_LUT_SIZE]), .result(tempCB.i));
                    end else if(lut_rem > 0) begin
                        // Lookahead
                        LUT #(.size(lut_rem), .fact(tempFbr[0:lut_rem-1])) LHLR_ (.sel(slh_rev[lut_offset +: lut_rem]), .result(tempLH.r));
                        LUT #(.size(lut_rem), .fact(tempFbi[0:lut_rem-1])) LHLI_ (.sel(slh_rev[lut_offset +: lut_rem]), .result(tempLH.i));
                        // Compute
                        LUT #(.size(lut_rem), .fact(tempFfr[0:lut_rem-1])) CFLR_ (.sel(scof[lut_offset +: lut_rem]), .result(tempCF.r));
                        LUT #(.size(lut_rem), .fact(tempFfi[0:lut_rem-1])) CFLI_ (.sel(scof[lut_offset +: lut_rem]), .result(tempCF.i));
                        LUT #(.size(lut_rem), .fact(tempFbr[0:lut_rem-1])) CBLR_ (.sel(scob_rev[lut_offset +: lut_rem]), .result(tempCB.r));
                        LUT #(.size(lut_rem), .fact(tempFbi[0:lut_rem-1])) CBLI_ (.sel(scob_rev[lut_offset +: lut_rem]), .result(tempCB.i));
                    end else begin
                        $error("Faulty LUT generation! LUT rest = %d", lut_rem);
                    end

                    // Sum results
                    if (lut_i == 0) begin
                        assign LH_in_part[0] = tempLH;
                        assign CF_in_part[0] = tempCF;
                        assign CB_in_part[0] = tempCB;
                    end else begin
                        CFPU #(.op(ADD)) LLH_ (.A(LH_in_part[lut_i-1]), .B(tempLH), .clk(clkDS), .result(LH_in_part[lut_i]));
                        CFPU #(.op(ADD)) LCF_ (.A(CF_in_part[lut_i-1]), .B(tempCF), .clk(clkDS), .result(CF_in_part[lut_i]));
                        CFPU #(.op(ADD)) LCB_ (.A(CB_in_part[lut_i-1]), .B(tempCB), .clk(clkDS), .result(CB_in_part[lut_i]));
                    end
                end

                assign LH_in = LH_in_part[LUTsplit-1];
                assign CF_in = CF_in_part[LUTsplit-1];
                assign CB_in = CB_in_part[LUTsplit-1];
            /*end else begin
                localparam floatType[0:`MAX_LUT_SIZE-1] testFbi = GetFbi(i, 0);
                localparam floatType[0:`MAX_LUT_SIZE-1] testFfr = GetFfr(i, 0);
                localparam floatType[0:`MAX_LUT_SIZE-1] testFbr = GetFbr(i, 0);
                localparam floatType[0:`MAX_LUT_SIZE-1] testFfi = GetFfi(i, 0);
                // Lookahead
                LUT #(.size(SampleWidth), .fact(testFbr[0:SampleWidth-1])) LHLR_ (.sel(slh_rev), .result(LH_in.r));
                LUT #(.size(SampleWidth), .fact(testFbi[0:SampleWidth-1])) LHLI_ (.sel(slh_rev), .result(LH_in.i));
                // Compute
                LUT #(.size(SampleWidth), .fact(testFfr[0:SampleWidth-1])) CFLR_ (.sel(scof), .result(CF_in.r));
                LUT #(.size(SampleWidth), .fact(testFfi[0:SampleWidth-1])) CFLI_ (.sel(scof), .result(CF_in.i));
                LUT #(.size(SampleWidth), .fact(testFbr[0:SampleWidth-1])) CBLR_ (.sel(scob_rev), .result(CB_in.r));
                LUT #(.size(SampleWidth), .fact(testFbi[0:SampleWidth-1])) CBLI_ (.sel(scob_rev), .result(CB_in.i));
            end*/

            localparam complex tempLb = cpow(Lbr[i], Lbi[i], OSR);
            localparam complex tempLf = cpow(Lfr[i], Lfi[i], OSR);

            complex LH_res, CF_out, CB_out, WF, WB;
            // Lookahead 
            RecursionModule #(.factorR(tempLb.r), .factorI(tempLb.i)) LHR_ (.in(LH_in), .rst(regProp & rst), .resetVal({rtof(0.0), rtof(0.0)}), .clk(clkDS), .out(LH_res));
            // Compute
            complex RF_in, RB_in;
            assign RF_in = validCompute ? CF_in : {rtof(0.0), rtof(0.0)};
            assign RB_in = validCompute ? CB_in : {rtof(0.0), rtof(0.0)};
            RecursionModule #(.factorR(tempLf.r), .factorI(tempLf.i)) CFR_ (.in(CF_in), .rst(rst), .resetVal({rtof(0.0), rtof(0.0)}), .clk(clkDS), .out(CF_out));
            RecursionModule #(.factorR(tempLb.r), .factorI(tempLb.i)) CBR_ (.in(CB_in), .rst(regProp & rst), .resetVal(LH_res), .clk(clkDS), .out(CB_out));
            
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
            CFPU #(.op(MULT)) WFR_ (.A(F_out), .B(WF), .clk(clkDS), .result(resF));
            CFPU #(.op(MULT)) WBR_ (.A(B_out), .B(WB), .clk(clkDS), .result(resB));

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
                FPU #(.op(ADD)) FINADDF (.A(partResF[i-1]), .B(forward), .clk(clkDS), .result(partResF[i]));
                FPU #(.op(ADD)) FINADDB (.A(partResB[i-1]), .B(backward), .clk(clkDS), .result(partResB[i]));
            end
        end
    endgenerate

    // Final final result
    FPU #(.op(ADD)) FINADD (.A(finF), .B(finB), .clk(clkDS), .result(finResult));
    always @(posedge clkDS) begin
        out = finResult;
    end
endmodule

`endif