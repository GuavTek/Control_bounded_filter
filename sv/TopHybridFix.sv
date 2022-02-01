`ifndef TOPHYBRIDFIX_SV_
`define TOPHYBRIDFIX_SV_

// n_int 9
// 60dB n_mant 15   depth 72
// 70dB n_mant 18   depth 180

`include "Data/Coefficients_Fixedpoint.sv"
`include "Util.sv"
`include "FixPU.sv"
`include "CFixPU.sv"
`include "FixRecursionModule.sv"
`include "FixLUT.sv"
`include "FixToFix.sv"
`include "Delay.sv"
`include "ClkDiv.sv"
`include "ValidCount.sv"
`include "InputReg.sv"

`define MAX_LUT_SIZE 6
`define COMB_ADDERS 3
`define OUT_WIDTH 14

module Hybrid_Fixed_top #(
    parameter   depth = 72,
                DSR = 12,
                n_mant = 15,
                n_int = 9
) (
    in, rst, clk, out, valid
);
    import Coefficients_Fx::N;
    localparam int DownSampleDepth = $ceil((0.0 + depth) / DSR);
    localparam SampleWidth = N*DSR; 
    localparam n_tot = n_int + n_mant;
    localparam Lookahead = depth;
    localparam int LUTahead_Layers = $clog2(int'($ceil((0.0 + N*Lookahead)/`MAX_LUT_SIZE)));
    localparam int LUTahead_Delay = $ceil((0.0 + LUTahead_Layers)/`COMB_ADDERS);
    localparam int LUTback_Layers = $clog2(int'($ceil((0.0 + SampleWidth)/`MAX_LUT_SIZE)));
    localparam int LUTback_Delay = $ceil((0.0 + LUTback_Layers)/`COMB_ADDERS) + 1;

    input wire [N-1:0] in;
    input logic rst, clk;
    output logic[`OUT_WIDTH-1:0] out;
    output logic valid;

    // Downsampled clock
    logic[$clog2(DSR)-1:0] dsrCount;      // Prescale counter
    logic clkDS;
    ClkDiv #(.DSR(DSR)) ClkDivider (.clkIn(clk), .rst(rst), .clkOut(clkDS), .cntOut(dsrCount));
    

    // Input shifting
    logic[N*DownSampleDepth*DSR-1:0] inShift;
    logic [SampleWidth-1:0] inSample;
    logic[$clog2(SampleWidth)-1:0] inSel;
    always @(posedge clkDS) begin
        inShift <= {inShift[N*DownSampleDepth*DSR-1-N*DSR:0], inSample};
    end

    InputReg #(.M(N), .DSR(DSR)) inReg (.clk(clk), .pos(dsrCount), .in(in), .out(inSample));

    logic[N*Lookahead-1:0] sampleahead;
    logic[SampleWidth-1:0] sampleback;

    assign sampleback = inShift[N*DownSampleDepth*DSR-1 -: SampleWidth];

    // Invert sample-order
    generate
        for(genvar i = 0; i < Lookahead; i++) begin
            assign sampleahead[N*i +: N] = inShift[N*(DownSampleDepth*DSR-i-1) +: N];
        end
    endgenerate

    // Count valid samples
    localparam int validTime = DownSampleDepth + 1 + (LUTahead_Delay > LUTback_Delay ? LUTahead_Delay : LUTback_Delay);
    localparam int validComp = DownSampleDepth + LUTback_Delay;
    logic validCompute;
    ValidCount #(.TopVal(validTime), .SecondVal(validComp)) vc1 (.clk(clkDS), .rst(rst), .out(valid), .out2(validCompute));

    // Outputs from generate blocks
    logic signed[n_tot:0] partResBack[N];
    logic signed[n_mant:0] lookaheadResult;

    // Scale results
    logic signed[`OUT_WIDTH-1:0] scaledResAhead, scaledResBack, finResult, delayedBack, delayedAhead;
    FixToFix #(.n_int_in(0), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) ResultScalerB (.in( lookaheadResult ), .out( scaledResAhead ) );
    FixToFix #(.n_int_in(n_int), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) ResultScalerF (.in( partResBack[N-1] ), .out( scaledResBack ) );

    localparam aheadDelay = LUTback_Delay - LUTahead_Delay + 1;
    localparam backDelay = LUTahead_Delay - LUTback_Delay - 1;
    generate
        if (backDelay > 0) begin
            Delay #(.size(`OUT_WIDTH), .delay(backDelay + 1)) backDelay (.in(scaledResBack), .clk(clkDS), .out(delayedBack));
        end else begin
            always @(posedge clkDS) begin
                delayedBack <= scaledResBack;
            end
        end

        if (aheadDelay > 0) begin
            Delay #(.size(`OUT_WIDTH), .delay(aheadDelay + 1)) aheadDelay (.in(scaledResAhead), .clk(clkDS), .out(delayedAhead));
        end else begin
            always @(posedge clkDS) begin
                delayedAhead <= scaledResAhead;
            end
        end
    endgenerate
    
    

    // Final final result
    FixPU #(.op(FPU_p::ADD), .n_int(0), .n_mant(`OUT_WIDTH-1)) FINADD (.A(delayedAhead), .B(delayedBack), .clk(clkDS), .result(finResult));
    always @(posedge clkDS) begin
        out <= {!finResult[`OUT_WIDTH-1], finResult[`OUT_WIDTH-2:0]};
    end

    // Generate FIR lookahead
    localparam logic signed[N*Lookahead-1:0][n_mant:0] hb_slice = GetConst #(.n_int(0), .n_mant(n_mant), .size(N*Lookahead))::Hb();
    FixLUT_Unit #(
        .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(N*Lookahead), .lut_size(`MAX_LUT_SIZE), .fact(hb_slice), .n_int(0), .n_mant(n_mant)) Lookahead_LUT (
        .sel(sampleahead), .clk(clkDS), .result(lookaheadResult)
    );

    // Generate lookback recursion
    generate 
        genvar i;
        for (i = 0; i < N ; i++ ) begin
            logic signed[n_tot:0] CF_inR, CF_inI;

            localparam logic signed[SampleWidth-1:0][n_tot:0] tempFfr = GetConst #(.n_int(n_int), .n_mant(n_mant), .size(SampleWidth))::Ffr(i);
            localparam logic signed[SampleWidth-1:0][n_tot:0] tempFfi = GetConst #(.n_int(n_int), .n_mant(n_mant), .size(SampleWidth))::Ffi(i);

            FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFfr), .n_int(n_int), .n_mant(n_mant)) CF_LUTr (
                .sel(sampleback), .clk(clkDS), .result(CF_inR)
            );

            FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(tempFfi), .n_int(n_int), .n_mant(n_mant)) CF_LUTi (
                .sel(sampleback), .clk(clkDS), .result(CF_inI)
            );

            localparam testr = Coefficients_Fx::Lfr[i];
            localparam testi = Coefficients_Fx::Lfi[i];
            localparam logic signed[1:0][n_tot:0] tempLf = GetConst #(.n_int(n_int), .n_mant(n_mant))::cpow(testr, testi, DSR);
            localparam logic signed[n_tot:0] resetZero = 'b0;

            logic signed[n_tot:0] CF_outR, CF_outI, WFR, WFI;

            // Compute
            logic signed[n_tot:0] RF_inR, RF_inI, RB_inR, RB_inI;
            assign RF_inR = validCompute ? CF_inR : 0;
            assign RF_inI = validCompute ? CF_inI : 0;
            FixRecursionModule #(
                .factorR(tempLf[0]), .factorI(tempLf[1]), .n_int(n_int), .n_mant(n_mant)) CFR_ (
                .inR(RF_inR), .inI(RF_inI), .rst(rst), .resetValR(resetZero), .resetValI(resetZero), .clk(clkDS || !rst), .outR(CF_outR), .outI(CF_outI)
            );

            assign WFR = GetConst #(.n_int(n_int), .n_mant(n_mant))::Wfr(i);
            assign WFI = GetConst #(.n_int(n_int), .n_mant(n_mant))::Wfi(i);

            // Save in registers to reduce timing requirements
            logic signed[n_tot:0] F_outR, F_outI;
            always @(posedge clkDS) begin
                F_outR <= CF_outR;
                F_outI <= CF_outI;
            end

            logic signed[n_tot:0] resFR, resFI;
            CFixPU #(.op(FPU_p::MULT), .n_int(n_int), .n_mant(n_mant)) WFR_ (.AR(F_outR), .AI(F_outI), .BR(WFR), .BI(WFI), .clk(clkDS), .resultR(resFR), .resultI(resFI));

            // Final add
            logic signed[n_tot:0] tempRes;
            always @(posedge clkDS) begin
                tempRes <= resFR;
            end

            if(i == 0) begin
                assign partResBack[0] = tempRes;
            end else begin
                FixPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) FINADDF (.A(partResBack[i-1]), .B(tempRes), .clk(clkDS), .result(partResBack[i]));
            end
        end
    endgenerate

endmodule

`endif 