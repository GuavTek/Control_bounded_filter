`ifndef TOPFIR_SV_
`define TOPFIR_SV_

`include "Data/Coefficients_Fixedpoint.sv"
`include "Util.sv"
`include "FPU.sv"
`include "LUT.sv"
`include "FloatToFix.sv"
`include "ClkDiv.sv"
`include "ValidCount.sv"
`include "InputReg.sv"

`define MAX_LUT_SIZE 7
`define COMB_ADDERS 3
`define OUT_WIDTH 14

module FIR_top #(
    parameter   Lookahead = 240,
                Lookback = 240,
                DSR = 12,
                n_exp = 8,
                n_mant = 23
) (
    in, rst, clk, out, valid
);
    import Coefficients_Fx::N;

    typedef struct packed { 
        logic sign; 
        logic[n_exp-1:0] exp;
        logic[n_mant-1:0] mant;
    } float_t;
        
    typedef struct packed {
        float_t r;
        float_t i;
    } complex_t;

    input wire[N-1:0] in;
    input logic rst, clk;
    output logic[`OUT_WIDTH-1:0] out;
    output logic valid;

    localparam Looktotal = Lookahead + Lookback;
    localparam int LookaheadLUTs = $ceil((0.0 + N*Lookahead)/`MAX_LUT_SIZE);
    localparam int LookbackLUTs = $ceil((0.0 + N*Lookback)/`MAX_LUT_SIZE);
    localparam int AddersNum = LookbackLUTs + LookaheadLUTs;
    localparam AdderLayers = $clog2(AddersNum);

    // Downsampled clock
    logic[$clog2(DSR)-1:0] dsrCount;      // Prescale counter
    logic clkDS;
    ClkDiv #(.DSR(DSR)) ClkDivider (.clkIn(clk), .rst(rst), .clkOut(clkDS), .cntOut(dsrCount));
    

    // Data valid counter
    localparam int validTime = $ceil((0.0 + Looktotal)/DSR) + $ceil((0.0 + AdderLayers)/`COMB_ADDERS) + 3;
    ValidCount #(.TopVal(validTime)) vc1 (.clk(clkDS), .rst(rst), .out(valid));

    // Input shifting
    logic[N*Looktotal-1:0] inShift;
    logic [N*DSR-1:0] inSample;
    always @(posedge clkDS) begin
        inShift <= {inShift[N*Looktotal-1-N*DSR:0], inSample};
    end

    InputReg #(.M(N), .DSR(DSR)) inReg (.clk(clk), .pos(dsrCount), .in(in), .out(inSample));
    

    logic[N*Lookahead-1:0] sampleahead;
    logic[N*Lookback-1:0] sampleback;

    assign sampleback = inShift[N*Looktotal-1:N*Lookahead];

    // Invert sample-order
    generate
        for(genvar i = 0; i < Lookahead; i++) begin
            assign sampleahead[N*i +: N] = inShift[N*(Lookahead-i-1) +: N];
        end
    endgenerate

    localparam coeff_mant = Coefficients_Fx::COEFF_BIAS;
    float_t lookbackResult, lookaheadResult, totResult;
    localparam logic signed[N*Lookback-1:0][63:0] hf_slice = GetConst #(.n_int(63-coeff_mant), .n_mant(coeff_mant), .size(N*Lookback))::Hf();
    localparam logic signed[N*Lookahead-1:0][63:0] hb_slice = GetConst #(.n_int(63-coeff_mant), .n_mant(coeff_mant), .size(N*Lookahead))::Hb();
    
    LUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(N*Lookahead), .lut_size(`MAX_LUT_SIZE), .fact(hb_slice), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t)) Lookahead_LUT (
                .sel(sampleahead), .clk(clkDS), .result(lookaheadResult)
            );

    LUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(N*Lookback), .lut_size(`MAX_LUT_SIZE), .fact(hf_slice), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t)) Lookback_LUT (
                .sel(sampleback), .clk(clkDS), .result(lookbackResult)
            );

    FPU #(.op(FPU_p::ADD), .float_t(float_t), .n_exp(n_exp), .n_mant(n_mant)) FinalAdder (.A(lookaheadResult), .B(lookbackResult), .clk(clkDS), .result(totResult)); 


    logic [`OUT_WIDTH-1:0] rectifiedResult;
    logic signed[`OUT_WIDTH-1:0] scaledResult;
    FloatToFix #(.n_int_out(0), .n_mant_out(`OUT_WIDTH-1), .n_exp_in(n_exp), .n_mant_in(n_mant), .float_t(float_t)) FinalScaler (.in( totResult ), .out( scaledResult ) );

    assign rectifiedResult[`OUT_WIDTH-1] = !scaledResult[`OUT_WIDTH-1];
    assign rectifiedResult[`OUT_WIDTH-2:0] = scaledResult[`OUT_WIDTH-2:0];

    // Final final result
    always @(posedge clkDS) begin
        out <= rectifiedResult;
    end
endmodule

`endif