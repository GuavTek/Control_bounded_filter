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
            logic signed[n_tot:0] CF_inR, CF_inI;

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

`endif
