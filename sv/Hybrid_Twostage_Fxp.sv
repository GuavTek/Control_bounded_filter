`ifndef HYBRID_TWOSTAGE_FXP_SV_
`define HYBRID_TWOSTAGE_FXP_SV_

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

`define MAX_LUT_SIZE 4
`define COMB_ADDERS 3
`define OUT_WIDTH 12

module Hybrid_Twostage_Fxp #(
    parameter   depth = 72,
                DSR1 = 2,
                DSR2 = 6,
                n_mant = 15,
                n_int = 9
) (
    in, rst, clk, out, valid
);
    import Coefficients_Fx::N;
    import Coefficients_Fx::M;

    localparam DSR = DSR1 * DSR2;
    localparam int DownSampleDepth = $ceil((0.0 + depth) / DSR);
    localparam SampleWidth = M*DSR; 
    localparam n_tot = n_int + n_mant;
    localparam Lookahead = depth;
    localparam ShiftDepth = DownSampleDepth * DSR;
    localparam int LUTahead_Layers = $clog2(int'($ceil((0.0 + M*Lookahead)/`MAX_LUT_SIZE)));
    localparam int LUTahead_Delay = $floor((0.0 + LUTahead_Layers)/`COMB_ADDERS);
    localparam int LUTback_Width = M*DSR1;
    localparam int LUTback_Layers = $clog2(int'($ceil((0.0 + LUTback_Width)/`MAX_LUT_SIZE)));
    localparam int LUTback_Delay = $floor((0.0 + LUTback_Layers)/`COMB_ADDERS) + 2;
    localparam int LUTback_Delay_Norm = $ceil((0.0 + LUTback_Delay)/DSR2);

    input wire [M-1:0] in;
    input logic rst, clk;
    output logic[`OUT_WIDTH-1:0] out;
    output logic valid;

    // Downsampled clocks
    logic[$clog2(DSR)-1:0] divCnt;
    logic[$clog2(DSR1)-1:0] divCnt1;
    logic[$clog2(DSR2)-1:0] divCnt2;
    logic clkDS, clkRecurse;
    ClkDiv #(.DSR(DSR1)) ClkDivider1 (.clkIn(clk), .rst(rst), .clkOut(clkRecurse), .cntOut(divCnt1));
    ClkDiv #(.DSR(DSR)) ClkDivider2 (.clkIn(clk), .rst(rst), .clkOut(clkDS), .cntOut(divCnt));

    // CDC 1: clk -> clkDS
    // Input register
    logic [SampleWidth-1:0] inSample;
    generate
        if (DSR > 1) begin
            always @(posedge clk) begin
                inSample <= {inSample[SampleWidth-M-1:0], in};
            end
        end else begin
            always @(posedge clk) begin
                inSample <= in;
            end
        end
    endgenerate
    

    // Input shift register
    logic[M*ShiftDepth-1:0] inShift;
    always @(posedge clkDS) begin
        inShift <= {inShift[M*ShiftDepth-1-M*DSR:0], inSample};
    end

    // CDC 2: clkDS -> clkRecurse
    // Shift lookback sample
    logic [SampleWidth-1:0] tempSampleback;
    logic [LUTback_Width-1:0] sampleback;
    generate
        if (DSR2 > 1) begin
            logic clkDS_edge;
            always @(posedge clkDS) begin
                if(!rst)
                    clkDS_edge <= 0;
                else
                    clkDS_edge <= !clkDS_edge;
            end

            logic prevEdge;
            always @(posedge clkRecurse) begin
                prevEdge <= clkDS_edge;
            end

            always @(posedge clkRecurse) begin
                if (clkDS_edge ^ prevEdge)
                    tempSampleback <= inShift[M*ShiftDepth-1-M*(DSR1*LUTback_Delay) -: SampleWidth];
                else
                    tempSampleback <= (tempSampleback << LUTback_Width);
            end
        end else begin
            always @(posedge clkRecurse) begin
                tempSampleback <= inShift[M*ShiftDepth-1-M*(DSR1*LUTback_Delay) -: SampleWidth];
            end
        end
    endgenerate
    
    always @(posedge clkRecurse) begin
        sampleback <= tempSampleback[SampleWidth-1 -: LUTback_Width];
    end

    // Prepare lookahead sample
    logic[M*Lookahead-1:0] sampleahead;
    generate
        // Invert sample-order
        for(genvar i = 0; i < Lookahead; i++) begin
            assign sampleahead[M*i +: M] = inShift[M*(ShiftDepth-i-1) +: M];
        end
    endgenerate

    // Count valid samples
    localparam int validTime = DownSampleDepth + 1 + LUTahead_Delay;// ((LUTahead_Delay > LUTback_Delay_Norm) ? LUTahead_Delay : LUTback_Delay_Norm);
    localparam int validComp = DownSampleDepth; // + LUTback_Delay_Norm;
    logic validCompute;
    ValidCount #(.TopVal(validTime), .SecondVal(validComp)) vc1 (.clk(clkDS), .rst(rst), .out(valid), .out2(validCompute));

    // Generate FIR lookahead
    logic signed[n_mant:0] lookaheadResult;
    GetHb #(.n_int(0), .n_mant(n_mant), .size(M*Lookahead)) hb_slice ();
    LUT_Unit_Fxp #(
        .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(M*Lookahead), .lut_size(`MAX_LUT_SIZE), .fact(hb_slice.Hb), .n_int(0), .n_mant(n_mant)) Lookahead_LUT (
        .sel(sampleahead), .clk(clkDS), .result(lookaheadResult)
    );

    // CDC 3: clkRecurse -> clkDS
    // Generate lookback recursion
    logic signed[n_tot:0] lookbackResult;
    LookbackRecursion #(
        .N(N), .M(M), .DSR(DSR1), .n_int(n_int), .n_mant(n_mant), .lut_size(`MAX_LUT_SIZE), .lut_comb(1), .adders_comb(`COMB_ADDERS) ) BackRec (
        .inSample(sampleback), .clkSample(clkRecurse), .clkResult(clkDS), .rst(rst), .validIn(validCompute), .result(lookbackResult) 
    );

    // Scale results
    logic signed[`OUT_WIDTH-1:0] scaledResAhead, scaledResBack, finResult, delayedBack, delayedAhead;
    Fxp_To_Fxp #(.n_int_in(0), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) ResultScalerB (.in( lookaheadResult ), .out( scaledResAhead ) );
    Fxp_To_Fxp #(.n_int_in(n_int), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) ResultScalerF (.in( lookbackResult ), .out( scaledResBack ) );

    // Equalize lookahead and lookback delays
    localparam int aheadDelay = 1 - LUTahead_Delay;
    localparam int backDelay = LUTahead_Delay - 1;
    Delay #(.size(`OUT_WIDTH), .delay(backDelay)) BackDelay (.in(scaledResBack), .clk(clkDS), .out(delayedBack));
    Delay #(.size(`OUT_WIDTH), .delay(aheadDelay)) AheadDelay (.in(scaledResAhead), .clk(clkDS), .out(delayedAhead));
    
    // Final final result
    FxpPU #(.op(FPU_p::ADD), .n_int(0), .n_mant(`OUT_WIDTH-1)) FINADD (.A(delayedAhead), .B(delayedBack), .clk(clkDS), .result(finResult));
    always @(posedge clkDS) begin
        out <= {!finResult[`OUT_WIDTH-1], finResult[`OUT_WIDTH-2:0]};
    end

endmodule

`endif