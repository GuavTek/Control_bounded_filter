`ifndef TOPHYBRIDFIX_SV_
`define TOPHYBRIDFIX_SV_

// n_int 9
// 60dB n_mant 15   depth 72
// 70dB n_mant 18   depth 180

`include "Util.sv"
`include "Data/Coefficients_Fixedpoint.sv"
//`include "Data/Coefficients_FixedpointPre.sv"
`include "FixPU.sv"
`include "CFixPU.sv"
`include "FixRecursionModule.sv"
`include "FixLUT.sv"
`include "FixToFix.sv"
`include "Delay.sv"

`define MAX_LUT_SIZE 6
`define COMB_ADDERS 1
`define OUT_WIDTH 14

module Hybrid_Fixed_top #(
    parameter   depth = 72,
                OSR1 = 2,
                OSR2 = 6,
                n_mant = 15,
                n_int = 9
) (
    in, rst, clk, out, valid
);
    import Coefficients_Fx::*;
    localparam OSR = OSR1 * OSR2;
    localparam int DownSampleDepth = $ceil((0.0 + depth) / OSR);
    localparam SampleWidth = N*OSR; 
    localparam n_tot = n_int + n_mant;
    localparam Lookahead = depth;
    localparam ShiftDepth = DownSampleDepth * OSR;
    localparam int LUTahead_Layers = $clog2(int'($ceil((0.0 + N*Lookahead)/`MAX_LUT_SIZE)));
    localparam int LUTahead_Delay = $ceil((0.0 + LUTahead_Layers)/`COMB_ADDERS);
    localparam int LUTback_Width = N*OSR1;
    localparam int LUTback_Layers = $clog2(int'($ceil((0.0 + LUTback_Width)/`MAX_LUT_SIZE)));
    localparam int LUTback_Delay = $ceil((0.0 + LUTback_Layers)/`COMB_ADDERS);

    input wire [N-1:0] in;
    input logic rst, clk;
    output logic[`OUT_WIDTH-1:0] out;
    output logic valid;

    // Downsampled clocks
    logic[$clog2(OSR)-1:0] osrCount;
    logic[$clog2(OSR1)-1:0] osrCount1;
    logic[$clog2(OSR2)-1:0] osrCount2;      // Prescale counter
    logic clkDS, clkRecurse, prevRst1, prevRst2;
    assign osrCount = osrCount1 + osrCount2 * OSR1;
    generate
        if(OSR2 > 1) begin
            always @(posedge clkRecurse) begin
                if ((!rst && prevRst2) || (osrCount2 == (OSR2-1)))
                    osrCount2 = 'b0;
                else
                    osrCount2++;

                if (1)
                    prevRst2 = rst;

                if (osrCount2 == 0)
                    clkDS = 1;
                if (osrCount2 == OSR2/2)
                    clkDS = 0;
                
            end
        end else begin
            assign clkDS = clkRecurse;
            assign osrCount2 = 0;
        end

        if(OSR1 > 1) begin
            always @(posedge clk) begin
                if ((!rst && prevRst1) || (osrCount1 == (OSR1-1)))
                    osrCount1 = 'b0;
                else
                    osrCount1++;

                if (1)
                    prevRst1 = rst;

                if (osrCount1 == 0)
                    clkRecurse = 1;
                if (osrCount1 == OSR1/2)
                    clkRecurse = 0;
                
            end
        end else begin
            assign clkRecurse = clk;
        end
    endgenerate 

    // Input shifting
    logic[N*ShiftDepth-1:0] inShift;
    logic [SampleWidth-1:0] inSample;
    logic[$clog2(SampleWidth)-1:0] inSel;
    always @(posedge clkDS) begin
        inShift <<= SampleWidth;
        inShift[SampleWidth-1:0] = inSample;
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
    logic[LUTback_Width-1:0] sampleback, slicedSampleBack[OSR2];

    generate
        for (genvar i = 0; i < OSR2 ; i++ ) begin
            assign slicedSampleBack[i] = inShift[N*ShiftDepth-1-N*OSR1*(i + LUTback_Delay) -: LUTback_Width];
        end
    endgenerate

    assign    sampleback = slicedSampleBack[osrCount2];

    // Invert sample-order
    generate
        for(genvar i = 0; i < Lookahead; i++) begin
            assign sampleahead[N*i +: N] = inShift[N*(ShiftDepth-i-1) +: N];
        end
    endgenerate

    // Count valid samples
    localparam int ValidDelay = DownSampleDepth + 2 + ((LUTahead_Delay > LUTback_Delay) ? LUTahead_Delay : 0);
    logic[$clog2(ValidDelay):0] validCount;
    logic validClk, validResult, validCompute;
    always @(posedge validClk) begin
        if(!rst) begin
            validCount = 'b0;
            validCompute = 'b0;
        end else begin
            validCount++;
            validCompute = validCompute | (validCount == (DownSampleDepth));
        end        
        
    end

    assign validResult = validCount == ValidDelay;
    assign validClk = clkDS && !validResult;
    assign valid = validResult;

    // Outputs from generate blocks
    logic signed[n_tot:0] partResBack[N];
    logic signed[n_mant:0] lookaheadResult;

    // Scale results
    logic signed[`OUT_WIDTH-1:0] scaledResAhead, scaledResBack, finResult, delayedBack, delayedAhead;
    FixToFix #(.n_int_in(0), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) ResultScalerB (.in( lookaheadResult ), .out( scaledResAhead ) );
    FixToFix #(.n_int_in(n_int), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) ResultScalerF (.in( partResBack[N-1] ), .out( scaledResBack ) );

    localparam backResDelay = LUTahead_Delay - 1;
    localparam aheadResDelay = 1 - LUTahead_Delay;
    generate
        if (backResDelay > 0)
            Delay #(.size(`OUT_WIDTH), .delay(backResDelay)) backDelay (.in(scaledResBack), .clk(clkDS), .out(delayedBack));
        else
            assign delayedBack = scaledResBack;

        if (aheadResDelay > 0)
            Delay #(.size(`OUT_WIDTH), .delay(aheadResDelay)) aheadDelay (.in(scaledResAhead), .clk(clkDS), .out(delayedAhead));
        else
            assign delayedAhead = scaledResAhead;
    endgenerate
    

    // Final final result
    FixPU #(.op(ADD), .n_int(0), .n_mant(`OUT_WIDTH-1)) FINADD (.A(delayedAhead), .B(delayedBack), .clk(clkDS), .result(finResult));
    always @(posedge clkDS) begin
        out = {!finResult[`OUT_WIDTH-1], finResult[`OUT_WIDTH-2:0]};
    end
    
    function automatic logic signed[N*Lookahead-1:0][n_mant:0] GetHb ();
        logic signed[N*Lookahead-1:0][n_mant:0] tempArray;

        for (int i = 0; i < N*Lookahead ; i++) begin
            logic signed[n_mant:0] temp = hb[i] >>> (COEFF_BIAS - n_mant);
            tempArray[i][n_mant:0] = temp;
        end
        return tempArray;
    endfunction

    function automatic logic signed[LUTback_Width-1:0][n_tot:0] GetFfr (int row);
        logic signed[LUTback_Width-1:0][n_tot:0] tempArray;
        for (int i = 0; i < LUTback_Width ; i++) begin
            tempArray[i][n_tot:0] = Ffr[row][i] >>> (COEFF_BIAS - n_mant);
        end
        return tempArray;
    endfunction

    function automatic logic signed[LUTback_Width-1:0][n_tot:0] GetFfi (int row);
        logic signed[LUTback_Width-1:0][n_tot:0] tempArray;
        for (int i = 0; i < LUTback_Width ; i++) begin
            tempArray[i][n_tot:0] = Ffi[row][i] >>> (COEFF_BIAS - n_mant);
        end
        return tempArray;
    endfunction

    function logic signed[1:0][n_tot:0] cpow_fixed(logic signed[63:0] r, logic signed[63:0] i, int exp);
        logic signed[1:0][n_tot:0] result;
        logic signed[63:0] tempR, tempI;
        tempR = r;
        tempI = i;
        for (int j = 1; j < exp ; j++ ) begin
            //cmulcc.r = (a.r * b.r) - (a.i * b.i);
            //cmulcc.i = (a.i * b.r) + (a.r * b.i);
            logic signed[127:0] tempReal, tempImag;
            tempReal = (tempR * r) - (tempI * i);
            tempImag = (tempI * r) + (tempR * i);
            tempR = tempReal >>> COEFF_BIAS;
            tempI = tempImag >>> COEFF_BIAS;
        end
        result[0][n_tot:0] = tempR >>> (COEFF_BIAS - n_mant);
        result[1][n_tot:0] = tempI >>> (COEFF_BIAS - n_mant);
        return result;
    endfunction


    // Generate FIR lookahead
    localparam logic signed[N*Lookahead-1:0][n_mant:0] hb_slice = GetHb();
    FixLUT_Unit #(
        .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(N*Lookahead), .lut_size(`MAX_LUT_SIZE), .fact(hb_slice), .n_int(0), .n_mant(n_mant)) Lookahead_LUT (
        .sel(sampleahead), .clk(clkDS), .result(lookaheadResult)
    );

    // Generate lookback recursion
    generate 
        genvar i;
        for (i = 0; i < N ; i++ ) begin
            logic signed[n_tot:0] CF_inR, CF_inI;
            
            localparam logic signed[LUTback_Width-1:0][n_tot:0] tempFfr = GetFfr(i);
            localparam logic signed[LUTback_Width-1:0][n_tot:0] tempFfi = GetFfi(i);

            FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(LUTback_Width), .lut_size(`MAX_LUT_SIZE), .fact(tempFfr), .n_int(n_int), .n_mant(n_mant)) CF_LUTr (
                .sel(sampleback), .clk(clkRecurse), .result(CF_inR)
            );

            FixLUT_Unit #(
                .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(LUTback_Width), .lut_size(`MAX_LUT_SIZE), .fact(tempFfi), .n_int(n_int), .n_mant(n_mant)) CF_LUTi (
                .sel(sampleback), .clk(clkRecurse), .result(CF_inI)
            );

            localparam logic signed[1:0][n_tot:0] tempLf = cpow_fixed(Lfr[i], Lfi[i], OSR1);
            localparam logic signed[n_tot:0] resetZero = 'b0;

            logic signed[n_tot:0] CF_outR, CF_outI, WFR, WFI;

            // Compute
            logic signed[n_tot:0] RF_inR, RF_inI, RB_inR, RB_inI;
            assign RF_inR = validCompute ? CF_inR : 0;
            assign RF_inI = validCompute ? CF_inI : 0;
            FixRecursionModule #(
                .factorR(tempLf[0]), .factorI(tempLf[1]), .n_int(n_int), .n_mant(n_mant)) CFR_ (
                .inR(RF_inR), .inI(RF_inI), .rst(rst), .resetValR(resetZero), .resetValI(resetZero), .clk(clkRecurse), .outR(CF_outR), .outI(CF_outI)
            );
            
            assign WFR = Wfr[i] >>> (COEFF_BIAS - n_mant);
            assign WFI = Wfi[i] >>> (COEFF_BIAS - n_mant);

            // Save in registers to relax timing requirements
            logic signed[n_tot:0] F_outR, F_outI;
            always @(posedge clkDS) begin
                F_outR = CF_outR;
                F_outI = CF_outI;
            end

            logic signed[n_tot:0] resFR, resFI;
            CFixPU #(.op(MULT), .n_int(n_int), .n_mant(n_mant)) WFR_ (.AR(F_outR), .AI(F_outI), .BR(WFR), .BI(WFI), .clk(clkDS), .resultR(resFR), .resultI(resFI));

            // Final add
            logic signed[n_tot:0] tempRes;
            always @(posedge clkDS) begin
                tempRes = resFR;
            end

            if(i == 0) begin
                assign partResBack[0] = tempRes;
            end else begin
                FixPU #(.op(ADD), .n_int(n_int), .n_mant(n_mant)) FINADDF (.A(partResBack[i-1]), .B(tempRes), .clk(clkDS), .result(partResBack[i]));
            end
        end
    endgenerate

endmodule

`endif