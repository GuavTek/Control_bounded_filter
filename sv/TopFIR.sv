`ifndef TOPFIR_SV_
`define TOPFIR_SV_

`include "Util.sv"
`include "Data/Coefficients_Fixedpoint.sv"
`include "FPU.sv"
`include "LUT.sv"
`include "FloatToFix.sv"

`define MAX_LUT_SIZE 7
`define COMB_ADDERS 3
`define OUT_WIDTH 14

module FIR_top #(
    parameter   Lookahead = 240,
                Lookback = 240,
                OSR = 12,
                n_exp = 8,
                n_mant = 23
) (
    in, rst, clk, out, valid
);
    import Coefficients_Fx::*;

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
    logic[$clog2(OSR)-1:0] osrCount;      // Prescale counter
    logic clkDS;
    generate
        if(OSR > 1) begin
            always @(posedge clk) begin
                if ((!rst) || (osrCount == (OSR-1)))
                    osrCount[$clog2(OSR)-1:0] = 'b0;
                else
                    osrCount++;

                if (osrCount == 0)
                    clkDS = 1;
                if (osrCount == OSR/2)
                    clkDS = 0;
                
            end
        end else begin
            assign clkDS = clk;
        end
    endgenerate 

    // Data valid counter
    localparam int validTime = $ceil((0.0 + Looktotal)/OSR) + $ceil((0.0 + AdderLayers)/`COMB_ADDERS) + 1;
    logic[$clog2(validTime):0] validCount;
    logic validClk, validResult;
    always @(posedge validClk, negedge rst) begin
        if(!rst)
            validCount = 0;
        else
            validCount++;
    end

    assign validResult = validCount == validTime;
    assign validClk = clkDS && !validResult;
    assign valid = validResult;

    // Input shifting
    logic[N*Looktotal-1:0] inShift;
    logic [N*OSR-1:0] inSample;
    logic[$clog2(N*OSR)-1:0] inSel;
    always @(posedge clkDS) begin
        inShift <<= N*OSR;
        inShift[N*OSR-1:0] = inSample;
    end

    // Reduce activity factor
    generate
        if (OSR > 1) begin
            always @(posedge clk) begin
                inSel = N*(OSR - osrCount)-1;
                inSample[inSel -: N] = in;
            end
        end else begin
            assign inSample = in;
        end
    endgenerate
    

    logic[N*Lookahead-1:0] sampleahead;
    logic[N*Lookback-1:0] sampleback;

    assign sampleback = inShift[N*Looktotal-1:N*Lookahead];

    // Invert sample-order
    generate
        for(genvar i = 0; i < Lookahead; i++) begin
            assign sampleahead[N*i +: N] = inShift[N*(Lookahead-i-1) +: N];
        end
    endgenerate

    function automatic logic signed[N*Lookahead-1:0][63:0] GetHb ();
        logic signed[N*Lookahead-1:0][63:0] tempArray;
        for (int i = 0; i < N*Lookahead ; i++) begin
            tempArray[i] = hb[i];
        end
        return tempArray;
    endfunction

    function automatic logic signed[N*Lookback-1:0][63:0] GetHf ();
        logic signed[N*Lookback-1:0][63:0] tempArray;
        for (int i = 0; i < N*Lookback ; i++) begin
            tempArray[i] = hf[i];
        end
        return tempArray;
    endfunction

    float_t lookbackResult, lookaheadResult, totResult;
    localparam logic signed[N*Lookback-1:0][63:0] hf_slice = GetHf();
    localparam logic signed[N*Lookahead-1:0][63:0] hb_slice = GetHb();
    
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
        out = rectifiedResult;
    end
endmodule

`endif