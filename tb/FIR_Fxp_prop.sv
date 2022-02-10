`ifndef FIR_FXP_PROP_SV_
`define FIR_FXP_PROP_SV_

`include "../sv/FIR_Fxp.sv"

module FIR_Fxp_prop #(
    parameter Lookahead = 240,
    parameter Lookback = 240,
    parameter DSR = 1
) (
    in,
    rst, clk,
    out,
    lutResults, adderResults
);
    import Coefficients_Fx::*;
    localparam Looktotal = Lookahead + Lookback;
    localparam int LookaheadLUTs = $ceil(N*Lookahead/`MAX_LUT_SIZE);
    localparam int LookbackLUTs = $ceil(N*Lookback/`MAX_LUT_SIZE);
    localparam int AddersNum = LookbackLUTs + LookaheadLUTs;
    localparam AdderLayers = $clog2(AddersNum);
    localparam n_int = `EXP_W;
    localparam n_mant = `MANT_W;
    localparam n_tot = n_int + n_mant;

    function automatic CheckHb (input int startIndex, logic signed[`MAX_LUT_SIZE-1:0][n_tot:0] slice);
        for (int i = 0; i < `MAX_LUT_SIZE ; i++) begin
            real tempReal = $floor(hb[startIndex + i] * 2.0**n_mant + 0.5);
            logic signed[n_tot:0] temp = $rtoi(tempReal);
            if(slice[i][n_tot:0] != temp)
                $error("Wrong hb loaded, got %1.10f 0x%0h, ideal val %1.10f, expecting %1.10f 0x%0h. Slice pos %2d, array pos %4d", $itor(slice[i]) * 2.0**(-n_mant), slice[i], hb[startIndex + i], $itor(temp) * 2.0**(-n_mant), temp, i, startIndex + i);
        end
    endfunction

    function automatic CheckHf (input int startIndex, logic signed[`MAX_LUT_SIZE-1:0][n_tot:0] slice);
        for (int i = 0; i < `MAX_LUT_SIZE ; i++) begin
            real tempReal = $floor(hf[startIndex + i] * 2.0**n_mant + 0.5);
            logic signed[n_tot:0] temp = $rtoi(tempReal);
            if(slice[i][n_tot:0] != temp)
                $error("Wrong hf loaded, got %1.10f 0x%0h, ideal val %1.10f, expecting %1.10f 0x%0h. Slice pos %2d, array pos %4d", $itor(slice[i]) * 2.0**(-n_mant), slice[i], hf[startIndex + i], $itor(temp) * 2.0**(-n_mant), temp, i, startIndex + i);
        end
    endfunction

    input wire [N-1:0] in;
    input logic rst, clk;
    input logic[11:0] out;
    input logic signed[n_tot:0] lutResults[AddersNum-1:0];
    input logic signed[n_tot:0] adderResults[GetFirstReg(AdderLayers):0];

    initial begin
        @(!rst)
        @(rst)

        for (int i = 0; i < LookaheadLUTs ; i++ ) begin
            automatic int offset = i*`MAX_LUT_SIZE;
            automatic logic signed[0:`MAX_LUT_SIZE-1][n_tot:0] temp_slice = FIR_Fixed_top.GetHb(offset);
            void'(CheckHb(offset, temp_slice));
        end

        for (int i = 0; i < LookbackLUTs ; i++ ) begin
            automatic int offset = i*`MAX_LUT_SIZE;
            automatic logic signed[0:`MAX_LUT_SIZE-1][n_tot:0] temp_slice = FIR_Fixed_top.GetHf(offset);
            void'(CheckHf(offset, temp_slice));
        end

    end

endmodule

`endif