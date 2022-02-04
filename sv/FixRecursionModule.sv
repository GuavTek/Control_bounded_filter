`ifndef FIXRECURSIONMODULE_SV_
`define FIXRECURSIONMODULE_SV_

`include "CFixPU.sv"
`include "Util.sv"

module FixRecursionModule #(
    parameter   factorR = 0,
                factorI = 0,
                n_int = 8,
                n_mant = 23
) (
    input logic signed[n_int+n_mant:0] inR, inI,
    input logic signed[n_int+n_mant:0] resetValR, resetValI,
    input logic rst, clk,
    output logic signed[n_int+n_mant:0] outR, outI
);
    logic signed[n_int+n_mant:0] prodR, prodI, sumR, sumI, prevR, prevI, prevSumR, prevSumI;
    logic resetting;
    assign outR = prevSumR;
    assign outI = prevSumI;
    assign prevR = resetting ? prevSumR : resetValR;
    assign prevI = resetting ? prevSumI : resetValI;

    CFixPU #(.op(FPU_p::MULT), .n_int(n_int), .n_mant(n_mant)) c1 (.AR(prevR), .AI(prevI), .BR(factorR), .BI(factorI), .clk(clk), .resultR(prodR), .resultI(prodI));
    CFixPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) c2 (.AR(prodR), .AI(prodI), .BR(inR), .BI(inI), .clk(clk), .resultR(sumR), .resultI(sumI));

    always @(posedge clk) begin : recurse
        resetting <= rst;
        prevSumR <= sumR;
        prevSumI <= sumI;
    end

endmodule

module LookbackRecursion #(
    parameter   N = 4,
                M = N,
                DSR = 12,
                n_int = 8,
                n_mant = 23,
                lut_size = 6,
                lut_comb = 1,
                adders_comb = 10
) (
    inSample,
    clk, rst, validIn,
    result
);
    localparam n_tot = n_int+n_mant;
    localparam SampleWidth = M*DSR;
    input logic[SampleWidth-1:0] inSample;
    input logic clk, rst, validIn;
    output logic signed[n_tot:0] result;

    logic signed[n_tot:0] partResBack[N];
    
    generate 
        for (genvar i = 0; i < N ; i++ ) begin

            // Import constants
            localparam logic signed[SampleWidth-1:0][n_tot:0] tempFfr = GetConst #(.n_int(n_int), .n_mant(n_mant), .size(SampleWidth))::Ffr(i);
            localparam logic signed[SampleWidth-1:0][n_tot:0] tempFfi = GetConst #(.n_int(n_int), .n_mant(n_mant), .size(SampleWidth))::Ffi(i);
            localparam tempLfr = Coefficients_Fx::Lfr[i];
            localparam tempLfi = Coefficients_Fx::Lfi[i];
            localparam logic signed[1:0][n_tot:0] tempLf = GetConst #(.n_int(n_int), .n_mant(n_mant))::cpow(tempLfr, tempLfi, DSR);
            localparam logic signed[n_tot:0] resetZero = 'b0;
            localparam logic signed[n_tot:0] WFR = GetConst #(.n_int(n_int), .n_mant(n_mant))::Wfr(i);
            localparam logic signed[n_tot:0] WFI = GetConst #(.n_int(n_int), .n_mant(n_mant))::Wfi(i);

            // Use LUTs to turn sample into a complex number
            logic signed[n_tot:0] CF_inR, CF_inI;
            FixLUT_Unit #(
                .lut_comb(lut_comb), .adders_comb(adders_comb), .size(SampleWidth), .lut_size(lut_size), .fact(tempFfr), .n_int(n_int), .n_mant(n_mant)) CF_LUTr (
                .sel(inSample), .clk(clk), .result(CF_inR)
            );

            FixLUT_Unit #(
                .lut_comb(lut_comb), .adders_comb(adders_comb), .size(SampleWidth), .lut_size(lut_size), .fact(tempFfi), .n_int(n_int), .n_mant(n_mant)) CF_LUTi (
                .sel(inSample), .clk(clk), .result(CF_inI)
            );

            // Compute when data is valid
            logic signed[n_tot:0] RF_inR, RF_inI, CF_outR, CF_outI;
            assign RF_inR = validIn ? CF_inR : 0;
            assign RF_inI = validIn ? CF_inI : 0;
            FixRecursionModule #(
                .factorR(tempLf[0]), .factorI(tempLf[1]), .n_int(n_int), .n_mant(n_mant)) CFR_ (
                .inR(RF_inR), .inI(RF_inI), .rst(rst), .resetValR(resetZero), .resetValI(resetZero), .clk(clk || !rst), .outR(CF_outR), .outI(CF_outI)
            );

            // Save in registers to reduce timing requirements
            logic signed[n_tot:0] F_outR, F_outI;
            always @(posedge clk) begin
                F_outR <= CF_outR;
                F_outI <= CF_outI;
            end

            // Multiply by factor W
            logic signed[n_tot:0] resFR, resFI;
            CFixPU #(.op(FPU_p::MULT), .n_int(n_int), .n_mant(n_mant)) WFR_ (.AR(F_outR), .AI(F_outI), .BR(WFR), .BI(WFI), .clk(clk), .resultR(resFR), .resultI(resFI));

            // Assign to array
            always @(posedge clk) begin
                partResBack[i] <= resFR;
            end
        end
    endgenerate

    // Final sum
    FixSum #(.size(N), .n_int(n_int), .n_mant(n_mant), .adders_comb(N)) sum1 (.in(partResBack), .clk(clk), .out(result));

endmodule


module LookaheadRecursion #(
    parameter   N = 4,
                M = N,
                DSR = 12,
                n_int = 8,
                n_mant = 23,
                lut_size = 6,
                lut_comb = 1,
                adders_comb = 10 
) (
    inSample, lookaheadSample,
    clk, rst, validIn, propagate,
    result
);
    localparam n_tot = n_int + n_mant;
    localparam SampleWidth = M*DSR;
    input logic[SampleWidth-1:0] inSample, lookaheadSample;
    input logic clk, rst, validIn, propagate;
    output logic signed[n_tot:0] result;

    logic signed[n_tot:0] partResAhead[N];

    // Must reverse sample order for LUTs
    wire[SampleWidth-1:0] lookaheadSample_rev, inSample_rev;
    generate
        genvar j;
        for (j = 0; j < DSR; j++ ) begin
            assign lookaheadSample_rev[N*j +: N] = lookaheadSample[N*(DSR-j-1) +: N];
            assign inSample_rev[N*j +: N] = inSample[N*(DSR-j-1) +: N];
        end
    endgenerate
    
    generate 
        for ( genvar i = 0; i < N ; i++ ) begin
            
            // Import constants
            localparam logic signed[SampleWidth-1:0][n_tot:0] tempFbr = GetConst #(.n_int(n_int), .n_mant(n_mant), .size(SampleWidth))::Fbr(i);
            localparam logic signed[SampleWidth-1:0][n_tot:0] tempFbi = GetConst #(.n_int(n_int), .n_mant(n_mant), .size(SampleWidth))::Fbi(i);
            localparam tempLbr = Coefficients_Fx::Lbr[i];
            localparam tempLbi = Coefficients_Fx::Lbi[i];
            localparam logic signed[1:0][n_tot:0] tempLb = GetConst #(.n_int(n_int), .n_mant(n_mant))::cpow(tempLbr, tempLbi, DSR);
            localparam logic signed[n_tot:0] resetZero = 'b0;
            localparam logic signed[n_tot:0] WBR = GetConst #(.n_int(n_int), .n_mant(n_mant))::Wbr(i);
            localparam logic signed[n_tot:0] WBI = GetConst #(.n_int(n_int), .n_mant(n_mant))::Wbi(i);

            // Use LUTs to turn sample into a complex number
            logic signed[n_tot:0] CB_inR, CB_inI, LH_inR, LH_inI;
            FixLUT_Unit #(
                .lut_comb(lut_comb), .adders_comb(adders_comb), .size(SampleWidth), .lut_size(lut_size), .fact(tempFbr), .n_int(n_int), .n_mant(n_mant)) LH_LUTr (
                .sel(lookaheadSample_rev), .clk(clk), .result(LH_inR)
                );

            FixLUT_Unit #(
                .lut_comb(lut_comb), .adders_comb(adders_comb), .size(SampleWidth), .lut_size(lut_size), .fact(tempFbr), .n_int(n_int), .n_mant(n_mant)) CB_LUTr (
                .sel(inSample_rev), .clk(clk), .result(CB_inR)
            );

            FixLUT_Unit #(
                .lut_comb(lut_comb), .adders_comb(adders_comb), .size(SampleWidth), .lut_size(lut_size), .fact(tempFbi), .n_int(n_int), .n_mant(n_mant)) LH_LUTi (
                .sel(lookaheadSample_rev), .clk(clk), .result(LH_inI)
                );

            FixLUT_Unit #(
                .lut_comb(lut_comb), .adders_comb(adders_comb), .size(SampleWidth), .lut_size(lut_size), .fact(tempFbi), .n_int(n_int), .n_mant(n_mant)) CB_LUTi (
                .sel(inSample_rev), .clk(clk), .result(CB_inI)
            );


            // Calculate Lookahead 
            logic signed[n_tot:0] LH_resR, LH_resI;
            FixRecursionModule #(.factorR(tempLb[0][n_tot:0]), .factorI(tempLb[1][n_tot:0]), .n_int(n_int), .n_mant(n_mant)) LHR_ (
                .inR(LH_inR), .inI(LH_inI), .rst(propagate & rst), .resetValR(resetZero), .resetValI(resetZero), .clk(clk || !rst), .outR(LH_resR), .outI(LH_resI)
                );

            // Compute when data is valid
            logic signed[n_tot:0] RB_inR, RB_inI, CB_outR, CB_outI;
            assign RB_inR = validIn ? CB_inR : 0;
            assign RB_inI = validIn ? CB_inI : 0;
            FixRecursionModule #(.factorR(tempLb[0][n_tot:0]), .factorI(tempLb[1][n_tot:0]), .n_int(n_int), .n_mant(n_mant)) CBR_ (
                .inR(RB_inR), .inI(RB_inI), .rst(propagate & rst), .resetValR(LH_resR), .resetValI(LH_resI), .clk(clk || !rst), .outR(CB_outR), .outI(CB_outI)
                );

            // Save in registers to reduce timing requirements
            logic signed[n_tot:0] B_outR, B_outI;
            always @(posedge clk) begin
                B_outR <= CB_outR;
                B_outI <= CB_outI;
            end

            // Multiply by factor W
            logic signed[n_tot:0] resBR, resBI;
            CFixPU #(.op(FPU_p::MULT), .n_int(n_int), .n_mant(n_mant)) WBR_ (.AR(B_outR), .AI(B_outI), .BR(WBR), .BI(WBI), .clk(clk), .resultR(resBR), .resultI(resBI));

            // Assign to array
            always @(posedge clk) begin
                partResAhead[i] <= resBR;
            end

        end
    endgenerate
    
    // Final sum
    FixSum #(.size(N), .n_int(n_int), .n_mant(n_mant), .adders_comb(N)) sum1 (.in(partResAhead), .clk(clk), .out(result));

endmodule

`endif
