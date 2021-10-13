`ifndef TOPFIR_SV_
`define TOPFIR_SV_

`include "Util.sv"
`include "Data/Coefficients.sv"
`include "FPU.sv"
`include "LUT.sv"

`define MAX_LUT_SIZE 6

module FIR_top #(
    parameter Lookahead = 240,
    parameter Lookback = 240,
    parameter N = 3,
    parameter OSR = 1
) (
    input wire [N-1:0] in,
    input logic rst, clk,
    output floatType out
);
    import Coefficients::*;
    localparam Looktotal = Lookahead + Lookback;
    localparam int LookaheadLUTs = $ceil(N*Lookahead/`MAX_LUT_SIZE);
    localparam int LookbackLUTs = $ceil(N*Lookback/`MAX_LUT_SIZE);
    localparam int AddersNum = LookbackLUTs + LookaheadLUTs;
    localparam AdderLayers = $clog2(AddersNum);

    // Downsampled clock
    logic[$clog2(OSR):0] osrCount;      // Prescale counter
    logic clkDS;
    generate
        if(OSR > 1) begin
            always @(posedge clk) begin
                osrCount++;
                if (osrCount == OSR)
                    osrCount = 0;
            end

            // MSb of counter is prescaled clock, not symmetrical for all OSR
            // Rising edge when osrCount = 0
            assign clkDS = !osrCount[$clog2(OSR)];
        end else begin
            assign clkDS = clk;
        end
    endgenerate


    // Shift register
    logic[N*Looktotal-1:0] inShift;
    always @(posedge clkDS) begin
        inShift[N*Looktotal-1:N] = inShift[N*Looktotal-N-1:0];
        inShift[N-1:0] = in;
    end

    wire[N*Lookahead-1:0] sampleahead;
    wire[N*Lookback-1:0] sampleback;
    assign sampleback = inShift[N*Looktotal-1:N*Lookahead];

    // Invert sample-order
    generate
        genvar i;
        for(i = 0; i < Lookahead; i++) begin
            assign sampleahead[N*i +: N] = inShift[N*(Lookahead-i-1) +: N];
        end
    endgenerate

    function int GetAdderNum(int n);
        automatic real temp = AddersNum;
        for(int i = 0; i < n; i++)
            temp = $ceil(temp/2);
        temp = $floor(temp/2);
        $info("AdderNum returning %d", temp);
        GetAdderNum = temp;
    endfunction

    function int GetRegsNum(int n);
        automatic real temp = AddersNum;
        for (int i = 0; i <= n; i++)
            temp = $ceil(temp/2);
        GetRegsNum = temp;
    endfunction

    function int GetFirstReg(int n);
        automatic int temp = 0;
        for (int i = 1; i < n; i++)
            temp += GetRegsNum(i-1);
        GetFirstReg = temp;
    endfunction

    function automatic floatType[0:`MAX_LUT_SIZE-1] GetHb (int startIndex);
        floatType[0:`MAX_LUT_SIZE-1] tempArray;
        floatType temp;
        for (int i = 0; i < `MAX_LUT_SIZE ; i++) begin
            tempArray[i] = rtof(hb[startIndex + i]);
        end
        return tempArray;
    endfunction

    function automatic floatType[0:`MAX_LUT_SIZE-1] GetHf (int startIndex);
        floatType[0:`MAX_LUT_SIZE-1] tempArray;
        for (int i = 0; i < `MAX_LUT_SIZE ; i++) begin
            tempArray[i] = rtof(hf[startIndex + i]);
        end
        return tempArray;
    endfunction

    floatType lutResults[AddersNum-1:0];
    floatType adderResults[GetFirstReg(AdderLayers):0];
    // Generate LUTs
    generate 
        localparam LookaheadRest = (N*Lookahead)% `MAX_LUT_SIZE;
        localparam LookbackRest = (N*Lookback) % `MAX_LUT_SIZE;

        for (i = 0; i < LookaheadLUTs ; i++ ) begin
            localparam offset = i*`MAX_LUT_SIZE;
            localparam floatType[0:`MAX_LUT_SIZE-1] hb_slice = GetHb(offset);
            if (i < $floor(N*Lookahead/`MAX_LUT_SIZE)) begin
                LUT #(.size(`MAX_LUT_SIZE), .fact(hb_slice)) lut_ (.sel(sampleahead[offset +: `MAX_LUT_SIZE]), .result(lutResults[i]));
            end else if (LookaheadRest > 0) begin
                LUT #(.size(LookaheadRest), .fact(hb_slice[0:LookaheadRest-1])) CFL_ (.sel(sampleahead[offset +: LookaheadRest]), .result(lutResults[i]));
            end else
                $error("Faulty LUT generation! Lookahead rest = %d", LookaheadRest);
        end
        
        for (i = 0; i < LookbackLUTs; i++ ) begin
            localparam offset = i*`MAX_LUT_SIZE;
            localparam floatType[0:`MAX_LUT_SIZE-1] hf_slice = GetHf(offset);
            if (i < $floor(N*Lookback/`MAX_LUT_SIZE)) begin
                LUT #(.size(`MAX_LUT_SIZE), .fact(hf_slice)) lut_ (.sel(sampleback[offset +: `MAX_LUT_SIZE]), .result(lutResults[LookaheadLUTs + i]));
            end else if (LookbackRest > 0) begin
                LUT #(.size(LookbackRest), .fact(hf_slice[0:LookbackRest-1])) CFL_ (.sel(sampleback[offset +: LookbackRest]), .result(lutResults[LookaheadLUTs + i]));
            end else
                $error("Faulty LUT generation! Lookback rest = %d", LookbackRest);
        end
    endgenerate

    // Generate adders
    generate
    genvar ii;
        $info("Generating adders");
        for (i = 0; i < AdderLayers ; i++ ) begin
            $info("Starting adder layer %d", i);
            localparam addfloor = GetAdderNum(i);
            $info("Number of adders %d", addfloor);
            localparam addceil = GetRegsNum(i);
            $info("Number of regs %d", addceil);
            localparam firstRes = GetFirstReg(i);
            $info("Start of last layer %d", firstRes);
            localparam nextRes = GetFirstReg(i+1);
            $info("Start of current layer %d", nextRes);
            for ( ii = 0; ii < addceil; ii++) begin
                floatType tempResult;
                if ( i == 0 ) begin
                    if ( ii < addfloor ) begin
                        FPU #(.op(ADD)) adder_ (.A(lutResults[2*ii]), .B(lutResults[2*ii + 1]), .result(tempResult));
                    end else begin
                        assign tempResult = lutResults[2*ii];
                    end
                end else begin
                    if ( ii < addfloor) begin
                        FPU #(.op(ADD)) adder_ (.A(adderResults[firstRes + 2*ii]), .B(adderResults[firstRes + 2*ii + 1]), .result(tempResult));
                    end else begin
                        assign tempResult = adderResults[firstRes + 2*ii];
                    end
                end

                always @(posedge clkDS) begin
                    adderResults[nextRes + ii] = tempResult;
                end
            end
            
        end
    endgenerate

    // Final final result
    always @(posedge clkDS) begin
        out = adderResults[GetFirstReg(AdderLayers)];
    end
endmodule

`endif