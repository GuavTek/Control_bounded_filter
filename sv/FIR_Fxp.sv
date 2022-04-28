`ifndef FIR_FXP_SV_
`define FIR_FXP_SV_

`include "Util.sv"
`include "FxpPU.sv"
`include "LUT_Fxp.sv"
`include "Fxp_To_Fxp.sv"
`include "ClkDiv.sv"
`include "ValidCount.sv"
`include "InputReg.sv"

`define MAX_LUT_SIZE 4
`define COMB_ADDERS 3
`define OUT_WIDTH 12

module FIR_Fxp #(
    parameter Lookahead = 96,
    parameter Lookback = 96,
    parameter DSR = 12,
    parameter n_int = 0,
    parameter n_mant = 14
) ( 
    in, rst, clk, out, valid
);
    import Coefficients_Fx::N;
    import Coefficients_Fx::M;
    
    input wire [M-1:0] in;
    input logic rst, clk;
    output logic[`OUT_WIDTH-1:0] out;
    output logic valid;

    localparam Looktotal = Lookahead + Lookback;
    localparam int LookaheadLUTs = $ceil((0.0 + M*Lookahead)/`MAX_LUT_SIZE);
    localparam int LookbackLUTs = $ceil((0.0 + M*Lookback)/`MAX_LUT_SIZE);
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
    logic [M*DSR-1:0] inSample;
    generate
        if(DSR > 1) begin
            always @(posedge clk) begin
                inSample <= {inSample[M*DSR-M-1:0], in};
            end
        end else begin
            always @(posedge clk) begin
                inSample <= in;
            end
        end
    endgenerate

    // Sample shift-register
    logic[M*Looktotal-1:0] inShift;
    always @(posedge clkDS) begin
        inShift <= {inShift[M*Looktotal-1-M*DSR:0], inSample};
    end

    // Prepare lookback samples
    logic[M*Lookback-1:0] sampleback;
    assign sampleback = inShift[M*Looktotal-1:M*Lookahead];

    // Prepare lookahead samples
    logic[M*Lookahead-1:0] sampleahead;
    generate
        // Invert sample-order
        for(genvar i = 0; i < Lookahead; i++) begin
            assign sampleahead[M*i +: M] = inShift[M*(Lookahead-i-1) +: M];
        end
    endgenerate

    logic signed[n_tot:0] lookaheadResult;
    logic signed[n_tot:0] lookbackResult;

    // Load constants
    GetHb #(.n_int(n_int), .n_mant(n_mant), .size(M*Lookahead)) hb_slice ();
    GetHf #(.n_int(n_int), .n_mant(n_mant), .size(M*Lookback)) hf_slice ();
    
    // Calculate lookahead
    LUT_Unit_Fxp #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(M*Lookahead), .lut_size(`MAX_LUT_SIZE), .fact( hb_slice.Hb ), .n_int(n_int), .n_mant(n_mant)) Lookahead_LUT (
                .sel(sampleahead), .clk(clkDS), .result(lookaheadResult)
            );

    // Calculate lookback
    LUT_Unit_Fxp #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(M*Lookback), .lut_size(`MAX_LUT_SIZE), .fact( hf_slice.Hf ), .n_int(n_int), .n_mant(n_mant)) Lookback_LUT (
                .sel(sampleback), .clk(clkDS), .result(lookbackResult)
            );

    // Calculate final result
    logic signed[n_tot:0] totResult;
    FxpPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) FinalAdder (.A(lookaheadResult), .B(lookbackResult), .clk(clkDS), .result(totResult)); 

    // Format the result
    logic [`OUT_WIDTH-1:0] rectifiedResult;
    logic signed[`OUT_WIDTH-1:0] scaledResult;
    Fxp_To_Fxp #(.n_int_in(n_int), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) FinalScaler (.in( totResult ), .out( scaledResult ) );

    assign rectifiedResult[`OUT_WIDTH-1] = !scaledResult[`OUT_WIDTH-1];
    assign rectifiedResult[`OUT_WIDTH-2:0] = scaledResult[`OUT_WIDTH-2:0];

    // Final final result
    always @(posedge clkDS) begin
        out <= rectifiedResult;
    end
endmodule

`endif
