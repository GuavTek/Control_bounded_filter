`ifndef TOPCUMULFIX_SV_
`define TOPCUMULFIX_SV_

// WARNING, IS NOT FEASIBLE!
// n_int 121516561948752151651967876561
// 60dB n_mant 14
// 70dB n_mant 16

`include "Util.sv"
`include "Data/Coefficients_Fixedpoint.sv"
`include "FixPU.sv"
`include "CFixPU.sv"
`include "FixRecursionModule.sv"
`include "FixLUT.sv"
`include "FixToFix.sv"

`define MAX_LUT_SIZE 6
`define COMB_ADDERS 1
`define OUT_WIDTH 14

virtual class FixedPoint#(parameter mant_in = 1, mant_out = 1, tot_out = 1);
    static function logic signed[1:0][tot_out:0] cpow(logic signed[63:0] r, logic signed[63:0] i, int exp);
        logic signed[1:0][tot_out:0] result;
        logic signed[63:0] tempR, tempI;
        tempR = r;
        tempI = i;
        for (int j = 1; j < exp ; j++ ) begin
            //cmulcc.r = (a.r * b.r) - (a.i * b.i);
            //cmulcc.i = (a.i * b.r) + (a.r * b.i);
            logic signed[127:0] tempReal, tempImag;
            tempReal = (tempR * r) - (tempI * i);
            tempImag = (tempI * r) + (tempR * i);
            tempR = tempReal >>> mant_in;
            tempI = tempImag >>> mant_in;
        end
        result[0][tot_out:0] = tempR >>> (mant_in - mant_out);
        result[1][tot_out:0] = tempI >>> (mant_in - mant_out);
        return result;
    endfunction

    static function logic signed[1:0][tot_out:0] cmult(logic signed[63:0] ar, logic signed[63:0] ai, logic signed[63:0] br, logic signed[63:0] bi);
        logic signed[1:0][tot_out:0] result;
        logic signed[127:0] tempR, tempI;
        tempR = (ar * br) - (ai * bi);
        tempI = (ai * br) + (ar * bi);
        result[0][tot_out:0] = tempR >>> (2*mant_in - mant_out);
        result[1][tot_out:0] = tempI >>> (2*mant_in - mant_out);
        return result;
    endfunction
endclass

module Cumulative_Fixed_top #(
    parameter depth = 180,
    parameter DSR = 1,
    parameter n_mant = 14,
    parameter n_int = 9
) (
    in, rst, clk, out, valid
);
    import Coefficients_Fx::*;
    localparam int DownSampleDepth = $ceil(0.0 + depth / DSR);
    localparam SampleWidth = N*DSR;
    localparam n_tot = n_int + n_mant;
    localparam LUT_Delay = $clog2(int'($ceil((0.0 + SampleWidth)/`MAX_LUT_SIZE)));

    input wire [N-1:0] in;
    input logic rst, clk;
    output logic[`OUT_WIDTH-1:0] out;
    output logic valid;

    // Downsampled clock
    logic[$clog2(DSR)-1:0] dsrCount = 0;      // Prescale counter
    logic clkDS, rstPrev;
    generate
        if(DSR > 1) begin
            always @(posedge clk) begin
                if(!rst && rstPrev) begin
                    dsrCount = 0;
                end else if (dsrCount == (DSR-1)) begin
                    dsrCount = 0;
                    clkDS = 1;
                end else
                    dsrCount++;
                rstPrev = rst;
                
                if (dsrCount == DSR/2)
                    clkDS = 0;
            end
        end else begin
            assign clkDS = clk;
        end
    endgenerate

    // Shifted input
    logic[SampleWidth-1:0] inShiftTemp;
    logic[DownSampleDepth:0][SampleWidth-1:0] inShift;
    always @(posedge clkDS) begin
        inShift = inShift << SampleWidth;
        inShift[0] = inShiftTemp;
    end
    // Generates shift register if DSR > 1
    generate
        if (DSR > 1) begin
            always @(posedge clk) begin
                inShiftTemp = inShiftTemp << N;
                inShiftTemp[N-1:0] = in;
            end
        end else begin
            assign inShiftTemp = in;
        end
    endgenerate

    // Count valid samples
    localparam ValidDelay = DownSampleDepth + 4;
    logic[$clog2(ValidDelay):0] validCount;
    logic validResult, validCompute, validAhead;
    always @(posedge clkDS) begin
        if(!rst) begin
            validCount = 'b0;
            validCompute = 'b0;
            validAhead = 'b0;
        end else if (!validResult) begin
            validCount++;
        end   
        validCompute |= validCount == DownSampleDepth + LUT_Delay;
        validAhead |= 1;//validCount == LUT_Delay;
    end

    assign validResult = validCount == ValidDelay;
    assign valid = validResult;

    logic[SampleWidth-1:0] LHA_Sample, LHS_Sample, LB_Sample;
    assign LHA_Sample = inShift[0][SampleWidth-1:0];
    assign LHS_Sample = inShift[DownSampleDepth][SampleWidth-1:0];
    assign LB_Sample = inShift[DownSampleDepth][SampleWidth-1:0];

    // Must reverse sample order for backward recursion LUTs
    wire[SampleWidth-1:0] LHA_Rev, LHS_Rev;
    generate
        genvar j;
        for (j = 0; j < DSR; j++ ) begin
            assign LHA_Rev[N*j +: N] = LHA_Sample[N*(DSR-j-1) +: N];
            assign LHS_Rev[N*j +: N] = LHS_Sample[N*(DSR-j-1) +: N];
        end
    endgenerate
    
    function automatic logic signed[1:0][SampleWidth-1:0][n_tot:0] GetLoopAdd (int row, logic signed[63:0] r, logic signed[63:0] i);
        logic signed[63:0] tempR, tempI;
        logic signed[127:0] tempReal, tempImag;
        logic signed[1:0][SampleWidth-1:0][n_tot:0] result;

        tempR = r;
        tempI = i;
        for (int j = 1; j < int'(DSR * (DownSampleDepth-1)) ; j++ ) begin
            tempReal = (tempR * r) - (tempI * i);
            tempImag = (tempI * r) + (tempR * i);
            tempR = tempReal >>> COEFF_BIAS;
            tempI = tempImag >>> COEFF_BIAS;
        end

        for (int i = 0; i < DSR ; i++) begin
            for (int j = 0; j < N ; j++) begin
                tempReal = (Fbr[row][j] * tempR) - (Fbi[row][j] * tempI);
                tempImag = (Fbi[row][j] * tempR) + (Fbr[row][j] * tempI);
                result[0][i*N + j] = tempReal >>> (2*COEFF_BIAS - n_mant);
                result[1][i*N + j] = tempImag >>> (2*COEFF_BIAS - n_mant);
            end
            tempReal = (tempR * r) - (tempI * i);
            tempImag = (tempI * r) + (tempR * i);
            tempR = tempReal >>> COEFF_BIAS;
            tempI = tempImag >>> COEFF_BIAS;
        end
        return result;
    endfunction

    function automatic logic signed[1:0][SampleWidth-1:0][n_tot:0] GetLoopSub (logic signed[SampleWidth-1:0][n_tot:0] addr, logic signed[SampleWidth-1:0][n_tot:0] addi, logic signed[n_tot:0] loopr, logic signed[n_tot:0] loopi);
        logic signed[1:0][SampleWidth-1:0][n_tot:0] result;
        logic signed[127:0] tempReal, tempImag;

        result[0] = addr;
        result[1] = addi;

        for (int i = 0; i < SampleWidth ; i++) begin
            for (int j = 0; j < DownSampleDepth ; j++) begin
                tempReal = (result[0][i] * loopr) - (result[1][i] * loopi);
                tempImag = (result[1][i] * loopr) + (result[0][i] * loopi);
                result[0][i] = tempReal >>> n_mant;
                result[1][i] = tempImag >>> n_mant;
            end
        end
        return result;
    endfunction

    function automatic logic signed[SampleWidth-1:0][n_tot:0] GetFfr (int row);
        logic signed[SampleWidth-1:0][n_tot:0] tempArray;
        for (int i = 0; i < SampleWidth ; i++) begin
            tempArray[i] = Ffr[row][i] >>> (COEFF_BIAS - n_mant);
        end
        return tempArray;
    endfunction

    function automatic logic signed[SampleWidth-1:0][n_tot:0] GetFfi (int row);
        logic signed[SampleWidth-1:0][n_tot:0] tempArray;
        for (int i = 0; i < SampleWidth ; i++) begin
            tempArray[i] = Ffi[row][i] >>> (COEFF_BIAS - n_mant);
        end
        return tempArray;
    endfunction

    // Outputs from generate blocks
    logic signed[n_tot:0] partResA[N], partResB[N];

    generate 
        genvar i;
        for (i = 0; i < N ; i++ ) begin
            // Prepare coefficients
            localparam logic signed[63:0] invahead_r = (128'(1) << 2*COEFF_BIAS)/Lbr[i];
            localparam logic signed[63:0] invahead_i = (128'(1) << 2*COEFF_BIAS)/Lbi[i];
            localparam logic signed[1:0][n_tot:0] loopahead_factor = FixedPoint#(COEFF_BIAS, n_mant, n_tot)::cpow(invahead_r, invahead_i, DSR);
            localparam logic signed[1:0][n_tot:0] loopback_factor = FixedPoint#(COEFF_BIAS, n_mant, n_tot)::cpow(Lfr[i], Lfi[i], DSR);

            localparam logic signed[1:0][SampleWidth-1:0][n_tot:0] aheadadd_factor = GetLoopAdd (i, Lbr[i], Lbi[i]);
            localparam logic signed[SampleWidth-1:0][n_tot:0] aheadadd_fr = aheadadd_factor[0];
            localparam logic signed[SampleWidth-1:0][n_tot:0] aheadadd_fi = aheadadd_factor[1];
            localparam logic signed[1:0][SampleWidth-1:0][n_tot:0] aheadsub_factor = GetLoopSub (aheadadd_fr, aheadadd_fi, loopahead_factor[0], loopahead_factor[1]);
            localparam logic signed[SampleWidth-1:0][n_tot:0] aheadsub_fr = aheadsub_factor[0];
            localparam logic signed[SampleWidth-1:0][n_tot:0] aheadsub_fi = aheadsub_factor[1];
            localparam logic signed[SampleWidth-1:0][n_tot:0] back_factorR = GetFfr(i);
            localparam logic signed[SampleWidth-1:0][n_tot:0] back_factorI = GetFfi(i);

            logic signed[n_tot:0] LHA_inR, LHA_inI, LHS_inR, LHS_inI, LB_inR, LB_inI;
            FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(aheadadd_fr), .n_int(n_int), .n_mant(n_mant)) LookaheadAdd_LUTr (
                .sel(LHA_Rev), .clk(clkDS), .result(LHA_inR)
                );

            FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(aheadsub_fr), .n_int(n_int), .n_mant(n_mant)) LookaheadSub_LUTr (
                .sel(LHS_Rev), .clk(clkDS), .result(LHS_inR)
                );

            FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(back_factorR), .n_int(n_int), .n_mant(n_mant)) Lookback_LUTr (
                .sel(LB_Sample), .clk(clkDS), .result(LB_inR)
            );

            FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(aheadadd_fi), .n_int(n_int), .n_mant(n_mant)) LookaheadAdd_LUTi (
                .sel(LHA_Rev), .clk(clkDS), .result(LHA_inI)
                );

            FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(aheadsub_fi), .n_int(n_int), .n_mant(n_mant)) LookaheadSub_LUTi (
                .sel(LHS_Rev), .clk(clkDS), .result(LHS_inI)
                );

            FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(SampleWidth), .lut_size(`MAX_LUT_SIZE), .fact(back_factorI), .n_int(n_int), .n_mant(n_mant)) Lookback_LUTi (
                .sel(LB_Sample), .clk(clkDS), .result(LB_inI)
            );

            logic signed[n_tot:0] LHSV_inR, LHSV_inI, LHAV_inR, LHAV_inI, LBV_inR, LBV_inI, LH_DiffR, LH_DiffI;
            assign LHSV_inR = validCompute ? LHS_inR : 0;
            assign LHAV_inR = validAhead ? LHA_inR : 0;
            assign LBV_inR = validCompute ? LB_inR : 0;
            assign LHSV_inI = validCompute ? LHS_inI : 0;
            assign LHAV_inI = validAhead ? LHA_inI : 0;
            assign LBV_inI = validCompute ? LB_inI : 0;
            assign LH_DiffR = LHAV_inR - LHSV_inR;
            assign LH_DiffI = LHAV_inI - LHSV_inI;

            logic signed[n_tot:0] LH_resR, LH_resI, LB_resR, LB_resI, WFR, WFI, WBR, WBI;
            FixRecursionModule #(.factorR(loopahead_factor[0]), .factorI(loopahead_factor[1]), .n_int(n_int), .n_mant(n_mant)) Lookahead_Recursion (
                .inR(LH_DiffR), .inI(LH_DiffI), .rst(rst), .resetValR(0), .resetValI(0), .clk(clkDS), .outR(LH_resR), .outI(LH_resI)
                );
                
            FixRecursionModule #(.factorR(loopback_factor[0]), .factorI(loopback_factor[1]), .n_int(n_int), .n_mant(n_mant)) Lookback_Recursion (
                .inR(LBV_inR), .inI(LBV_inI), .rst(rst), .resetValR(0), .resetValI(0), .clk(clkDS), .outR(LB_resR), .outI(LB_resI)
                );
            
            assign WFR = Wfr[i] >>> (COEFF_BIAS - n_mant);
            assign WFI = Wfi[i] >>> (COEFF_BIAS - n_mant);
            assign WBR = Wbr[i] >>> (COEFF_BIAS - n_mant);
            assign WBI = Wbi[i] >>> (COEFF_BIAS - n_mant);

            // Save in registers to reduce timing requirements
            logic signed[n_tot:0] A_outR, A_outI, B_outR, B_outI;
            always @(posedge clkDS) begin
                A_outR = LH_resR;
                A_outI = LH_resI;
                B_outR = LB_resR;
                B_outI = LB_resI;
            end

            logic signed[n_tot:0] A_resR, A_resI, B_resR, B_resI;
            CFixPU #(.op(FPU_p::MULT), .n_int(n_int), .n_mant(n_mant)) WFR_ (.AR(B_outR), .AI(B_outI), .BR(WFR), .BI(WFI), .clk(clkDS), .resultR(B_resR), .resultI(B_resI));
            CFixPU #(.op(FPU_p::MULT), .n_int(n_int), .n_mant(n_mant)) WBR_ (.AR(A_outR), .AI(A_outI), .BR(WBR), .BI(WBI), .clk(clkDS), .resultR(A_resR), .resultI(A_resI));



            // Final add
            logic signed[n_tot:0] aheadResult, backResult;
            always @(posedge clkDS) begin
                backResult = B_resR;
                aheadResult = A_resR;
            end

            if(i == 0) begin
                assign partResA[0] = aheadResult;
                assign partResB[0] = backResult;
            end else begin
                FixPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) FINADDA (.A(partResA[i-1]), .B(aheadResult), .clk(clkDS), .result(partResA[i]));
                FixPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) FINADDB (.A(partResB[i-1]), .B(backResult), .clk(clkDS), .result(partResB[i]));
            end
        end
    endgenerate

    // Scale results
    logic signed[`OUT_WIDTH-1:0] scaledResB, scaledResA, finResult;
    FixToFix #(.n_int_in(n_int), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) ResultScalerB (.in( partResB[N-1] ), .out( scaledResB ) );
    FixToFix #(.n_int_in(n_int), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) ResultScalerA (.in( partResA[N-1] ), .out( scaledResA ) );

    // Final final result
    FixPU #(.op(FPU_p::ADD), .n_int(0), .n_mant(`OUT_WIDTH-1)) FINADD (.A(scaledResA), .B(scaledResB), .clk(clkDS), .result(finResult));
    always @(posedge clkDS) begin
        out = {!finResult[`OUT_WIDTH-1], finResult[`OUT_WIDTH-2:0]};
    end
endmodule

`endif