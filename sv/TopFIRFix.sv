`ifndef TOPFIRFIX_SV_
`define TOPFIRFIX_SV_

`ifndef EXP_W
    `define EXP_W 0
`endif  // EXP_W
`ifndef MANT_W
    `define MANT_W 14
`endif  // MANT_W

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
    parameter OSR = 12
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
    localparam n_int = `EXP_W;
    localparam n_mant = `MANT_W;
    localparam n_tot = n_int + n_mant;

    // Downsampled clock
    logic[$clog2(OSR)-1:0] osrCount;      // Prescale counter
    logic clkDS, prevRst;
    generate
        if(OSR > 1) begin
            always @(posedge clk) begin
                if (!rst && prevRst)
                    osrCount = 0;
                else 
                    osrCount++;
                prevRst = rst;

                if (osrCount == int'($floor(OSR/2)))
                    clkDS = 0;
                if (osrCount == OSR) begin
                    osrCount = 0;
                    clkDS = 1;
                end
            end
        end else begin
            assign clkDS = clk;
        end
    endgenerate
    
    // Data valid counter
    localparam int validTime = $ceil((0.0 + Looktotal)/OSR) + $ceil(AdderLayers/`COMB_ADDERS) + 2;
    logic[$clog2(validTime):0] validCount;
    logic validResult;
    always @(posedge clkDS) begin
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
    always @(posedge clkDS) begin
        inShift[N*Looktotal-1:N*OSR] = inShift[N*Looktotal-N*OSR-1:0];
        inShift[N*OSR-1:0] = inSample;
    end

    // Reduce activity factor
    generate
        if (OSR > 1) begin
            always @(posedge clk) begin
                //inSample[N*OSR-1:N] = inSample[N*OSR-N-1:0];
                inSample[N*(OSR - osrCount)-1 -: N] = in;
            end
        end else begin
            assign inSample = in;
        end
    endgenerate
    

    logic[N*Lookahead-1:0] sampleahead;
    logic[N*Lookback-1:0] sampleback;

    
    //always @(posedge clkDS) begin
        assign sampleback = inShift[N*Looktotal-1:N*Lookahead];
    //end

    // Invert sample-order
    generate
        genvar i;
        for(i = 0; i < Lookahead; i++) begin
            //always @(posedge clkDS) begin
                assign sampleahead[N*i +: N] = inShift[N*(Lookahead-i-1) +: N];
            //end
        end
    endgenerate

    function automatic logic signed[N*Lookahead-1:0][n_tot:0] GetHb (int startIndex);
        logic signed[N*Lookahead-1:0][n_tot:0] tempArray;

        for (int i = 0; i < N*Lookahead ; i++) begin
            logic signed[n_tot:0] temp = hb[startIndex + i] >>> (COEFF_BIAS - n_mant);
            tempArray[i][n_tot:0] = temp;
        end
        return tempArray;
    endfunction

    function automatic logic signed[N*Lookback-1:0][n_tot:0] GetHf (int startIndex);
        logic signed[N*Lookback-1:0][n_tot:0] tempArray;
        
        for (int i = 0; i < N*Lookback ; i++) begin
            logic signed[n_tot:0] temp = hf[startIndex + i] >>> (COEFF_BIAS - n_mant);
            tempArray[i][n_tot:0] = temp;
        end
        return tempArray;
    endfunction 

    logic signed[n_tot:0] lookbackResult, lookaheadResult, totResult;
    localparam logic signed[N*Lookback-1:0][n_tot:0] hf_slice = GetHf(0);
    localparam logic signed[N*Lookback-1:0][n_tot:0] hb_slice = GetHb(0);
    
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