`ifndef TOPFIRFIX_SV_
`define TOPFIRFIX_SV_

`include "Util.sv"
`include "Data/Coefficients_Fixedpoint.sv"
`include "FixPU.sv"
`include "FixLUT.sv"
`include "FixToFix.sv"

`define MAX_LUT_SIZE 6
`define COMB_ADDERS 3
`define OUT_WIDTH 14

module FIR_Fixed_top #(
    parameter Lookahead = 96,
    parameter Lookback = 96,
    parameter OSR = 12,
    parameter n_int = 0,
    parameter n_mant = 14
) ( 
    in, rst, clk, out, valid
);
    import Coefficients_Fx::hf;
    import Coefficients_Fx::hb;
    import Coefficients_Fx::N;
    import Coefficients_Fx::COEFF_BIAS;

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
    logic[$clog2(OSR)-1:0] osrCount;      // Prescale counter
    logic clkDS;
    logic prevRst;
    generate
        if(OSR > 1) begin
            always @(posedge clk) begin
                if (!rst && prevRst)
                    osrCount = 0;
                else if (osrCount == (OSR-1)) begin
                    osrCount = 0;
                    clkDS = 1;
                end else
                    osrCount++;
                prevRst = rst;

                if (osrCount == OSR/2)
                    clkDS = 0;
                
            end
        end else begin
            assign clkDS = clk;
        end
    endgenerate 
    
    // Data valid counter
    localparam int validTime = $ceil((0.0 + Looktotal)/OSR) + $ceil((0.0 + AdderLayers)/`COMB_ADDERS) + 5;
    logic[$clog2(validTime):0] validCount;
    logic validResult;
    always @(posedge clkDS, negedge rst) begin
        if(!rst)
            validCount = 0;
        else if (!validResult)
            validCount++;
    end

    assign validResult = validCount == validTime;
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

    function automatic logic signed[N*Lookahead-1:0][n_tot:0] GetHb ();
        logic signed[N*Lookahead-1:0][n_tot:0] tempArray;

        for (int i = 0; i < N*Lookahead ; i++) begin
            logic signed[n_tot:0] temp = hb[i] >>> (COEFF_BIAS - n_mant);
            tempArray[i][n_tot:0] = temp;
        end
        return tempArray;
    endfunction

    function automatic logic signed[N*Lookback-1:0][n_tot:0] GetHf ();
        logic signed[N*Lookback-1:0][n_tot:0] tempArray;
        
        for (int i = 0; i < N*Lookback ; i++) begin
            logic signed[n_tot:0] temp = hf[i] >>> (COEFF_BIAS - n_mant);
            tempArray[i][n_tot:0] = temp;
        end
        return tempArray;
    endfunction 

    logic signed[n_tot:0] lookbackResult, lookaheadResult, totResult;
    localparam logic signed[N*Lookback-1:0][n_tot:0] hf_slice = GetHf();
    localparam logic signed[N*Lookahead-1:0][n_tot:0] hb_slice = GetHb();
    
    FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(N*Lookahead), .lut_size(`MAX_LUT_SIZE), .fact(hb_slice), .n_int(n_int), .n_mant(n_mant)) Lookahead_LUT (
                .sel(sampleahead), .clk(clkDS), .result(lookaheadResult)
            );

    FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(N*Lookback), .lut_size(`MAX_LUT_SIZE), .fact(hf_slice), .n_int(n_int), .n_mant(n_mant)) Lookback_LUT (
                .sel(sampleback), .clk(clkDS), .result(lookbackResult)
            );

    FixPU #(.op(ADD), .n_int(n_int), .n_mant(n_mant)) FinalAdder (.A(lookaheadResult), .B(lookbackResult), .clk(clkDS), .result(totResult)); 

    logic [`OUT_WIDTH-1:0] rectifiedResult;
    logic signed[`OUT_WIDTH-1:0] scaledResult;
    FixToFix #(.n_int_in(n_int), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) FinalScaler (.in( totResult ), .out( scaledResult ) );

    assign rectifiedResult[`OUT_WIDTH-1] = !scaledResult[`OUT_WIDTH-1];
    assign rectifiedResult[`OUT_WIDTH-2:0] = scaledResult[`OUT_WIDTH-2:0];

    // Final final result
    always @(posedge clkDS) begin
        out = rectifiedResult;
    end
endmodule

`endif
