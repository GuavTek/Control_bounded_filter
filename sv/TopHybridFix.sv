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
    localparam int LUTahead_Delay = $floor((0.0 + LUTahead_Layers)/`COMB_ADDERS);
    localparam int LUTback_Layers = $clog2(int'($ceil((0.0 + SampleWidth)/`MAX_LUT_SIZE)));
    localparam int LUTback_Delay = $floor((0.0 + LUTback_Layers)/`COMB_ADDERS) + 1;

    input wire [N-1:0] in;
    input logic rst, clk;
    output logic[`OUT_WIDTH-1:0] out;
    output logic valid;

    // Downsampled clock
    logic[$clog2(DSR)-1:0] divCnt;
    logic clkDS;
    ClkDiv #(.DSR(DSR)) ClkDivider (.clkIn(clk), .rst(rst), .clkOut(clkDS), .cntOut(divCnt));
    
    // Input register
    logic [SampleWidth-1:0] inSample;
    InputReg #(.M(N), .DSR(DSR)) inReg (.clk(clk), .pos(divCnt), .in(in), .out(inSample));

    // Input shift register
    logic[N*DownSampleDepth*DSR-1:0] inShift;
    always @(posedge clkDS) begin
        inShift <= {inShift[N*DownSampleDepth*DSR-1-N*DSR:0], inSample};
    end

    // Prepare sample for the lookback
    logic[SampleWidth-1:0] sampleback;
    assign sampleback = inShift[N*DownSampleDepth*DSR-1 -: SampleWidth];

    // Prepare samples for lookahead
    logic[N*Lookahead-1:0] sampleahead;
    generate
        // Invert sample order
        for(genvar i = 0; i < Lookahead; i++) begin
            assign sampleahead[N*i +: N] = inShift[N*(DownSampleDepth*DSR-i-1) +: N];
        end
    endgenerate

    // Count valid samples
    localparam int validTime = DownSampleDepth + 1 + (LUTahead_Delay > LUTback_Delay ? LUTahead_Delay : LUTback_Delay);
    localparam int validComp = DownSampleDepth + LUTback_Delay;
    logic validCompute;
    ValidCount #(.TopVal(validTime), .SecondVal(validComp)) vc1 (.clk(clkDS), .rst(rst), .out(valid), .out2(validCompute));

    // Generate FIR lookahead
    logic signed[n_mant:0] lookaheadResult;
    GetHb #(.n_int(0), .n_mant(n_mant), .size(N*Lookahead)) hb_slice ();
    FixLUT_Unit #(
        .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(N*Lookahead), .lut_size(`MAX_LUT_SIZE), .fact(hb_slice.Hb), .n_int(0), .n_mant(n_mant)) Lookahead_LUT (
        .sel(sampleahead), .clk(clkDS), .result(lookaheadResult)
    );

    // Generate lookback recursion
    logic signed[n_tot:0] lookbackResult;
    LookbackRecursion #(
        .N(N), .DSR(DSR), .n_int(n_int), .n_mant(n_mant), .lut_size(`MAX_LUT_SIZE), .lut_comb(1), .adders_comb(`COMB_ADDERS) ) BackRec (
        .inSample(sampleback), .clk(clkDS), .rst(rst), .validIn(validCompute), .result(lookbackResult) 
    );

    // Scale results
    logic signed[`OUT_WIDTH-1:0] scaledResAhead, scaledResBack, finResult, delayedBack, delayedAhead;
    FixToFix #(.n_int_in(0), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) ResultScalerB (.in( lookaheadResult ), .out( scaledResAhead ) );
    FixToFix #(.n_int_in(n_int), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) ResultScalerF (.in( lookbackResult ), .out( scaledResBack ) );

    // Equalize lookahead and lookback delays
    localparam aheadDelay = LUTback_Delay - LUTahead_Delay + 1;
    localparam backDelay = LUTahead_Delay - LUTback_Delay - 1;
    Delay #(.size(`OUT_WIDTH), .delay(backDelay)) BackDelay (.in(scaledResBack), .clk(clkDS), .out(delayedBack));
    Delay #(.size(`OUT_WIDTH), .delay(aheadDelay)) AheadDelay (.in(scaledResAhead), .clk(clkDS), .out(delayedAhead));
        
    // Final final result
    FixPU #(.op(FPU_p::ADD), .n_int(0), .n_mant(`OUT_WIDTH-1)) FINADD (.A(delayedAhead), .B(delayedBack), .clk(clkDS), .result(finResult));
    always @(posedge clkDS) begin
        out <= {!finResult[`OUT_WIDTH-1], finResult[`OUT_WIDTH-2:0]};
    end

endmodule

`endif 