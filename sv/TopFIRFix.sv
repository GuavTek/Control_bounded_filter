`ifndef TOPFIRFIX_SV_
`define TOPFIRFIX_SV_

`include "Data/Coefficients_Fixedpoint.sv"
`include "Util.sv"
`include "FixPU.sv"
`include "FixLUT.sv"
`include "FixToFix.sv"
`include "ClkDiv.sv"
`include "ValidCount.sv"
`include "InputReg.sv"

`define MAX_LUT_SIZE 6
`define COMB_ADDERS 3
`define OUT_WIDTH 14

module FIR_Fixed_top #(
    parameter Lookahead = 96,
    parameter Lookback = 96,
    parameter DSR = 12,
    parameter n_int = 0,
    parameter n_mant = 14
) ( 
    in, rst, clk, out, valid
);
    import Coefficients_Fx::N;

    input wire [N-1:0] in;
    input logic rst, clk;
    output logic[`OUT_WIDTH-1:0] out;
    output logic valid;

    localparam Looktotal = Lookahead + Lookback;
    localparam int LookaheadLUTs = $ceil((0.0 + N*Lookahead)/`MAX_LUT_SIZE);
    localparam int LookbackLUTs = $ceil((0.0 + N*Lookback)/`MAX_LUT_SIZE);
    localparam int AddersNum = LookbackLUTs + LookaheadLUTs;
    localparam AdderLayers = $clog2(AddersNum);
    localparam n_tot = n_int + n_mant;

    // Downsampled clock
    logic[$clog2(DSR)-1:0] divCnt;
    logic clkDS;
    ClkDiv #(.DSR(DSR)) ClkDivider (.clkIn(clk), .rst(rst), .clkOut(clkDS), .cntOut(divCnt));
    
    // Data valid counter
    localparam int validTime = $ceil((0.0 + Looktotal)/DSR) + $ceil((0.0 + AdderLayers)/(`COMB_ADDERS + 1)) + 3;
    logic dummyValid;
    ValidCount #(.TopVal(validTime)) vc1 (.clk(clkDS), .rst(rst), .out(valid), .out2(dummyValid));

    // Input register
    InputReg #(.M(N), .DSR(DSR)) inReg (.clk(clk), .pos(divCnt), .in(in), .out(inSample));

    // Sample shift-register
    logic[N*Looktotal-1:0] inShift;
    logic [N*DSR-1:0] inSample;
    always @(posedge clkDS) begin
        inShift <= {inShift[N*Looktotal-1-N*DSR:0], inSample};
    end

    // Prepare lookback samples
    logic[N*Lookback-1:0] sampleback;
    assign sampleback = inShift[N*Looktotal-1:N*Lookahead];

    // Prepare lookahead samples
    logic[N*Lookahead-1:0] sampleahead;
    generate
        // Invert sample-order
        for(genvar i = 0; i < Lookahead; i++) begin
            assign sampleahead[N*i +: N] = inShift[N*(Lookahead-i-1) +: N];
        end
    endgenerate

    // Load constants
    localparam logic signed[N*Lookback-1:0][n_tot:0] hf_slice = GetConst #(.n_int(n_int), .n_mant(n_mant), .size(N*Lookback))::Hf();
    localparam logic signed[N*Lookahead-1:0][n_tot:0] hb_slice = GetConst #(.n_int(n_int), .n_mant(n_mant), .size(N*Lookahead))::Hb();
    
    // Calculate lookahead
    logic signed[n_tot:0] lookaheadResult;
    FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(N*Lookahead), .lut_size(`MAX_LUT_SIZE), .fact(hb_slice), .n_int(n_int), .n_mant(n_mant)) Lookahead_LUT (
                .sel(sampleahead), .clk(clkDS), .result(lookaheadResult)
            );

    // Calculate lookback
    logic signed[n_tot:0] lookbackResult;
    FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(N*Lookback), .lut_size(`MAX_LUT_SIZE), .fact(hf_slice), .n_int(n_int), .n_mant(n_mant)) Lookback_LUT (
                .sel(sampleback), .clk(clkDS), .result(lookbackResult)
            );

    // Calculate final result
    logic signed[n_tot:0] totResult;
    FixPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) FinalAdder (.A(lookaheadResult), .B(lookbackResult), .clk(clkDS), .result(totResult)); 

    // Format the result
    logic [`OUT_WIDTH-1:0] rectifiedResult;
    logic signed[`OUT_WIDTH-1:0] scaledResult;
    FixToFix #(.n_int_in(n_int), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) FinalScaler (.in( totResult ), .out( scaledResult ) );

    assign rectifiedResult[`OUT_WIDTH-1] = !scaledResult[`OUT_WIDTH-1];
    assign rectifiedResult[`OUT_WIDTH-2:0] = scaledResult[`OUT_WIDTH-2:0];

    // Final final result
    always @(posedge clkDS) begin
        out <= rectifiedResult;
    end
endmodule

`endif
