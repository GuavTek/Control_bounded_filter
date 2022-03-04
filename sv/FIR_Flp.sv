`ifndef FIR_FLP_SV_
`define FIR_FLP_SV_

`include "Util.sv"
`include "FPU.sv"
`include "LUT_Flp.sv"
`include "Flp_To_Fxp.sv"
`include "ClkDiv.sv"
`include "ValidCount.sv"
`include "InputReg.sv"

`define MAX_LUT_SIZE 7
`define COMB_ADDERS 3
`define OUT_WIDTH 14

module FIR_Flp #(
    parameter   Lookahead = 240,
                Lookback = 240,
                DSR = 12,
                n_exp = 8,
                n_mant = 23
) (
    in, rst, clk, out, valid
);
    import Coefficients_Fx::N;
    import Coefficients_Fx::M;
    
    typedef struct packed { 
        logic sign; 
        logic[n_exp-1:0] exp;
        logic[n_mant-1:0] mant;
    } float_t;
        
    typedef struct packed {
        float_t r;
        float_t i;
    } complex_t;

    input wire[M-1:0] in;
    input logic rst, clk;
    output logic[`OUT_WIDTH-1:0] out;
    output logic valid;

    localparam Looktotal = Lookahead + Lookback;
    localparam int LookaheadLUTs = $ceil((0.0 + M*Lookahead)/`MAX_LUT_SIZE);
    localparam int LookbackLUTs = $ceil((0.0 + M*Lookback)/`MAX_LUT_SIZE);
    localparam int AddersNum = LookbackLUTs + LookaheadLUTs;
    localparam AdderLayers = $clog2(AddersNum);

    // Downsampled clock
    logic[$clog2(DSR)-1:0] dsrCount;      // Prescale counter
    logic clkDS;
    ClkDiv #(.DSR(DSR)) ClkDivider (.clkIn(clk), .rst(rst), .clkOut(clkDS), .cntOut(dsrCount));
    

    // Data valid counter
    localparam int validTime = $ceil((0.0 + Looktotal)/DSR) + $ceil((0.0 + AdderLayers)/`COMB_ADDERS) + 3;
    ValidCount #(.TopVal(validTime)) vc1 (.clk(clkDS), .rst(rst), .out(valid));

    // Input register
    logic [M*DSR-1:0] inSample;
    InputReg #(.M(M), .DSR(DSR)) inReg (.clk(clk), .pos(dsrCount), .in(in), .out(inSample));

    // Input shift-register
    logic[M*Looktotal-1:0] inShift;
    always @(posedge clkDS) begin
        inShift <= {inShift[M*Looktotal-1-M*DSR:0], inSample};
    end

    // Prepare lookback sample
    logic[M*Lookback-1:0] sampleback;
    assign sampleback = inShift[M*Looktotal-1:M*Lookahead];

    // Prepare lookahead samples
    logic[M*Lookahead-1:0] sampleahead;
    generate
        // Invert sample order
        for(genvar i = 0; i < Lookahead; i++) begin
            assign sampleahead[M*i +: M] = inShift[M*(Lookahead-i-1) +: M];
        end
    endgenerate

    localparam coeff_mant = Coefficients_Fx::COEFF_BIAS;
    GetHb #(.n_int(63-coeff_mant), .n_mant(coeff_mant), .size(M*Lookahead)) hb_slice ();
    GetHf #(.n_int(63-coeff_mant), .n_mant(coeff_mant), .size(M*Lookback)) hf_slice ();
    
    // Calculate lookahead
    float_t lookaheadResult;
    LUT_Unit_Flp #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(M*Lookahead), .lut_size(`MAX_LUT_SIZE), .fact(hb_slice.Hb), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t)) Lookahead_LUT (
                .sel(sampleahead), .clk(clkDS), .result(lookaheadResult)
            );

    // Calculate lookback
    float_t lookbackResult;
    LUT_Unit_Flp #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(M*Lookback), .lut_size(`MAX_LUT_SIZE), .fact(hf_slice.Hf), .f_exp(n_exp), .f_mant(n_mant), .float_t(float_t)) Lookback_LUT (
                .sel(sampleback), .clk(clkDS), .result(lookbackResult)
            );

    // Calculate final result
    float_t totResult;
    FPU #(.op(FPU_p::ADD), .float_t(float_t), .n_exp(n_exp), .n_mant(n_mant)) FinalAdder (.A(lookaheadResult), .B(lookbackResult), .clk(clkDS), .result(totResult)); 

    // Reformat and scale result
    logic [`OUT_WIDTH-1:0] rectifiedResult;
    logic signed[`OUT_WIDTH-1:0] scaledResult;
    Flp_To_Fxp #(.n_int_out(0), .n_mant_out(`OUT_WIDTH-1), .n_exp_in(n_exp), .n_mant_in(n_mant), .float_t(float_t)) FinalScaler (.in( totResult ), .out( scaledResult ) );

    assign rectifiedResult[`OUT_WIDTH-1] = !scaledResult[`OUT_WIDTH-1];
    assign rectifiedResult[`OUT_WIDTH-2:0] = scaledResult[`OUT_WIDTH-2:0];

    // Final final result
    always @(posedge clkDS) begin
        out <= rectifiedResult;
    end
endmodule

`endif