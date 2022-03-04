`ifndef HYBRIDFXP_SV_
`define HYBRIDFXP_SV_

// n_int 9
// 60dB n_mant 15   depth 72
// 70dB n_mant 18   depth 180

`include "Util.sv"
`include "FxpPU.sv"
`include "CFxpPU.sv"
`include "Recursion_Fxp.sv"
`include "LUT_Fxp.sv"
`include "Fxp_To_Fxp.sv"
`include "Delay.sv"
`include "ClkDiv.sv"
`include "ValidCount.sv"
`include "InputReg.sv"

`define MAX_LUT_SIZE 6
`define COMB_ADDERS 3
`define OUT_WIDTH 14

module Hybrid_Fxp #(
    parameter   depth = 72,
                DSR = 12,
                n_mant = 15,
                n_int = 9
) (
    in, rst, clk, out, valid
);
    import Coefficients_Fx::N;
    import Coefficients_Fx::M;
    
    localparam int DownSampleDepth = $ceil((0.0 + depth) / DSR);
    localparam SampleWidth = M*DSR; 
    localparam n_tot = n_int + n_mant;
    localparam Lookahead = depth;
    localparam int LUTahead_Layers = $clog2(int'($ceil((0.0 + M*Lookahead)/`MAX_LUT_SIZE)));
    localparam int LUTahead_Delay = $floor((0.0 + LUTahead_Layers)/`COMB_ADDERS);
    localparam int LUTback_Layers = $clog2(int'($ceil((0.0 + SampleWidth)/`MAX_LUT_SIZE)));
    localparam int LUTback_Delay = $floor((0.0 + LUTback_Layers)/`COMB_ADDERS) + 1;

    input wire [M-1:0] in;
    input logic rst, clk;
    output logic[`OUT_WIDTH-1:0] out;
    output logic valid;

    // Downsampled clock
    logic[$clog2(DSR)-1:0] divCnt;
    logic clkDS;
    ClkDiv #(.DSR(DSR)) ClkDivider (.clkIn(clk), .rst(rst), .clkOut(clkDS), .cntOut(divCnt));
    
    // Input register
    logic [SampleWidth-1:0] inSample;
    InputReg #(.M(M), .DSR(DSR)) inReg (.clk(clk), .pos(divCnt), .in(in), .out(inSample));

    // Input shift register
    logic[M*DownSampleDepth*DSR-1:0] inShift;
    always @(posedge clkDS) begin
        inShift <= {inShift[M*DownSampleDepth*DSR-1-M*DSR:0], inSample};
    end

    // Prepare sample for the lookback
    logic[SampleWidth-1:0] sampleback;
    assign sampleback = inShift[M*DownSampleDepth*DSR-1 -: SampleWidth];

    // Prepare samples for lookahead
    logic[M*Lookahead-1:0] sampleahead;
    generate
        // Invert sample order
        for(genvar i = 0; i < Lookahead; i++) begin
            assign sampleahead[M*i +: M] = inShift[M*(DownSampleDepth*DSR-i-1) +: M];
        end
    endgenerate

    // Count valid samples
    localparam int validTime = DownSampleDepth + 1 + (LUTahead_Delay > LUTback_Delay ? LUTahead_Delay : LUTback_Delay);
    localparam int validComp = DownSampleDepth + LUTback_Delay;
    logic validCompute;
    ValidCount #(.TopVal(validTime), .SecondVal(validComp)) vc1 (.clk(clkDS), .rst(rst), .out(valid), .out2(validCompute));

    // Generate FIR lookahead
    logic signed[n_mant:0] lookaheadResult;
    GetHb #(.n_int(0), .n_mant(n_mant), .size(M*Lookahead)) hb_slice ();
    LUT_Unit_Fxp #(
        .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(M*Lookahead), .lut_size(`MAX_LUT_SIZE), .fact(hb_slice.Hb), .n_int(0), .n_mant(n_mant)) Lookahead_LUT (
        .sel(sampleahead), .clk(clkDS), .result(lookaheadResult)
    );

    // Generate lookback recursion
    logic signed[n_tot:0] lookbackResult;
    LookbackRecursion #(
        .N(N), .M(M), .DSR(DSR), .n_int(n_int), .n_mant(n_mant), .lut_size(`MAX_LUT_SIZE), .lut_comb(1), .adders_comb(`COMB_ADDERS) ) BackRec (
        .inSample(sampleback), .clkSample(clkDS), .clkResult(clkDS), .rst(rst), .validIn(validCompute), .result(lookbackResult) 
    );

    // Scale results
    logic signed[`OUT_WIDTH-1:0] scaledResAhead, scaledResBack, finResult, delayedBack, delayedAhead;
    Fxp_To_Fxp #(.n_int_in(0), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) ResultScalerB (.in( lookaheadResult ), .out( scaledResAhead ) );
    Fxp_To_Fxp #(.n_int_in(n_int), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) ResultScalerF (.in( lookbackResult ), .out( scaledResBack ) );

    // Equalize lookahead and lookback delays
    localparam aheadDelay = LUTback_Delay - LUTahead_Delay + 1;
    localparam backDelay = LUTahead_Delay - LUTback_Delay - 1;
    Delay #(.size(`OUT_WIDTH), .delay(backDelay)) BackDelay (.in(scaledResBack), .clk(clkDS), .out(delayedBack));
    Delay #(.size(`OUT_WIDTH), .delay(aheadDelay)) AheadDelay (.in(scaledResAhead), .clk(clkDS), .out(delayedAhead));
        
    // Final final result
    FxpPU #(.op(FPU_p::ADD), .n_int(0), .n_mant(`OUT_WIDTH-1)) FINADD (.A(delayedAhead), .B(delayedBack), .clk(clkDS), .result(finResult));
    always @(posedge clkDS) begin
        out <= {!finResult[`OUT_WIDTH-1], finResult[`OUT_WIDTH-2:0]};
    end

endmodule

`endif 