`ifndef TOPFIR_PROP_SV_
`define TOPFIR_PROP_SV_

`include "../sv/TopFIR.sv"

module FIR_prop #(
    parameter Lookahead = 240,
    parameter Lookback = 240,
    parameter OSR = 1
) (
    in,
    rst, clk,
    out,
    lutResults, adderResults
);
    import Coefficients::*;
    localparam Looktotal = Lookahead + Lookback;
    localparam int LookaheadLUTs = $ceil(N*Lookahead/`MAX_LUT_SIZE);
    localparam int LookbackLUTs = $ceil(N*Lookback/`MAX_LUT_SIZE);
    localparam int AddersNum = LookbackLUTs + LookaheadLUTs;
    localparam AdderLayers = $clog2(AddersNum);

    function CheckHb (input int startIndex, floatType[0:`MAX_LUT_SIZE-1] slice);
        for (int i = 0; i < `MAX_LUT_SIZE ; i++) begin
            if(absr(ftor(slice[i]) - hb[startIndex + i]) > 0.01*absr(hb[startIndex + i]))
                $error("Wrong hb loaded, got %1.10f 0x%h, ideal val %1.10f, expecting %1.10f 0x%h. Slice pos %2d, array pos %4d", ftor(slice[i]), slice[i], hb[startIndex + i], ftor(rtof(hb[startIndex + i])), rtof(hb[startIndex + i]), i, startIndex + i);
        end
    endfunction

    function CheckHf (input int startIndex, floatType[0:`MAX_LUT_SIZE-1] slice);
        for (int i = 0; i < `MAX_LUT_SIZE ; i++) begin
            if(absr(ftor(slice[i]) - hf[startIndex + i]) > 0.01*absr(hf[startIndex + i]))
                $error("Wrong hf loaded, got %1.10f 0x%h, ideal val %1.10f, expecting %1.10f 0x%h. Slice pos %2d, array pos %4d", ftor(slice[i]), slice[i], hf[startIndex + i], ftor(rtof(hf[startIndex + i])), rtof(hf[startIndex + i]), i, startIndex + i);
        end
    endfunction

    input wire [N-1:0] in;
    input logic rst, clk;
    input floatType out;
    input floatType lutResults[AddersNum-1:0];
    input floatType adderResults[GetFirstReg(AdderLayers):0];

    initial begin
        @(!rst)
        @(rst)

        for (int i = 0; i < LookaheadLUTs ; i++ ) begin
            automatic int offset = i*`MAX_LUT_SIZE;
            automatic floatType[0:`MAX_LUT_SIZE-1] temp_slice = FIR_top.GetHb(offset);
            void'(CheckHb(offset, temp_slice));
        end

        for (int i = 0; i < LookbackLUTs ; i++ ) begin
            automatic int offset = i*`MAX_LUT_SIZE;
            automatic floatType[0:`MAX_LUT_SIZE-1] temp_slice = FIR_top.GetHf(offset);
            void'(CheckHf(offset, temp_slice));
        end

    end

endmodule

`endif