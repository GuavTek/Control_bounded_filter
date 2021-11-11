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
`define OUT_WIDTH 14

module FIR_Fixed_top #(
    parameter Lookahead = 96,
    parameter Lookback = 96,
    parameter OSR = 12
) ( 
    in, rst, clk, out, valid
);
    import Coefficients::hf;
    import Coefficients::hb;
    import Coefficients::N;
    import Coefficients::COEFF_BIAS;

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
    localparam int validTime = $ceil(Looktotal/OSR) + AdderLayers + 2;
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

    function automatic logic signed[`MAX_LUT_SIZE-1:0][n_tot:0] GetHb (int startIndex);
        logic signed[`MAX_LUT_SIZE-1:0][n_tot:0] tempArray;

        for (int i = 0; i < `MAX_LUT_SIZE ; i++) begin
            logic signed[n_tot:0] temp = hb[startIndex + i] >>> (COEFF_BIAS - n_mant);
            tempArray[i][n_tot:0] = temp;
        end
        return tempArray;
    endfunction


    function automatic logic signed[`MAX_LUT_SIZE-1:0][n_tot:0] GetHf (int startIndex);
        logic signed[`MAX_LUT_SIZE-1:0][n_tot:0] tempArray;
        
        for (int i = 0; i < `MAX_LUT_SIZE ; i++) begin
            logic signed[n_tot:0] temp = hf[startIndex + i] >>> (COEFF_BIAS - n_mant);
            tempArray[i][n_tot:0] = temp;
        end
        return tempArray;
    endfunction 

    /*
    virtual class GetHf#(parameter startIndex);
        static function logic signed[`MAX_LUT_SIZE-1:0][n_tot:0] Get();
            logic signed[`MAX_LUT_SIZE-1:0][n_tot:0] tempArray;

            for (int i = 0; i < `MAX_LUT_SIZE ; i++) begin
                localparam logic signed[n_tot:0] temp = (Coefficients_FIR1::hf[startIndex + i] * 2.0**n_mant);
                tempArray[i][n_tot:0] = temp;
            end
            return tempArray;
        endfunction
    endclass
    */

    logic signed[n_tot:0] lutResults[AddersNum-1:0];
    logic signed[n_tot:0] adderResults[GetFirstReg(AdderLayers):0];
    // Generate LUTs
    generate
        localparam LookaheadRest = (N*Lookahead)% `MAX_LUT_SIZE;
        localparam LookbackRest = (N*Lookback) % `MAX_LUT_SIZE;

        for (i = 0; i < LookaheadLUTs ; i++ ) begin : LUTb_Gen
            localparam offset = i*`MAX_LUT_SIZE;
            localparam logic signed[`MAX_LUT_SIZE-1:0][n_tot:0] hb_slice = GetHb(offset);
            if (i < $floor(N*Lookahead/`MAX_LUT_SIZE)) begin
                FixLUT #(.size(`MAX_LUT_SIZE), .n_int(n_int), .n_mant(n_mant), .fact(hb_slice)) lut_b (.sel(sampleahead[offset +: `MAX_LUT_SIZE]), .result(lutResults[i]));
            end else if (LookaheadRest > 0) begin
                FixLUT #(.size(LookaheadRest), .n_int(n_int), .n_mant(n_mant), .fact(hb_slice[LookaheadRest-1:0])) CFL_b (.sel(sampleahead[offset +: LookaheadRest]), .result(lutResults[i]));
            end else
                $error("Faulty LUT generation! Lookahead rest = %d", LookaheadRest);
        end
        
        for (i = 0; i < LookbackLUTs; i++ ) begin : LUTf_Gen
            localparam offset = i*`MAX_LUT_SIZE;
            localparam logic signed[`MAX_LUT_SIZE-1:0][n_tot:0] hf_slice = GetHf(offset);
            if (i < $floor(N*Lookback/`MAX_LUT_SIZE)) begin
                FixLUT #(.size(`MAX_LUT_SIZE), .n_int(n_int), .n_mant(n_mant), .fact(hf_slice)) lut_f (.sel(sampleback[offset +: `MAX_LUT_SIZE]), .result(lutResults[LookaheadLUTs + i]));
            end else if (LookbackRest > 0) begin
                FixLUT #(.size(LookbackRest), .n_int(n_int), .n_mant(n_mant), .fact(hf_slice[LookbackRest-1:0])) CFL_f (.sel(sampleback[offset +: LookbackRest]), .result(lutResults[LookaheadLUTs + i]));
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
                logic signed[n_tot:0] tempResult;
                if ( i == 0 ) begin
                    if ( ii < addfloor ) begin
                        FixPU #(.op(ADD), .n_int(n_int), .n_mant(n_mant)) adder_ (.A(lutResults[2*ii]), .B(lutResults[2*ii + 1]), .clk(clkDS), .result(tempResult));
                    end else begin
                        assign tempResult = lutResults[2*ii];
                    end
                end else begin
                    if ( ii < addfloor) begin
                        FixPU #(.op(ADD), .n_int(n_int), .n_mant(n_mant)) adder_ (.A(adderResults[firstRes + 2*ii]), .B(adderResults[firstRes + 2*ii + 1]), .clk(clkDS), .result(tempResult));
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

    logic [`OUT_WIDTH-1:0] rectifiedResult;
    logic signed[`OUT_WIDTH-1:0] scaledResult;
    FixToFix #(.n_int_in(n_int), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) FinalScaler (.in( adderResults[GetFirstReg(AdderLayers)] ), .out( scaledResult ) );

    assign rectifiedResult[`OUT_WIDTH-1] = !scaledResult[`OUT_WIDTH-1];
    assign rectifiedResult[`OUT_WIDTH-2:0] = scaledResult[`OUT_WIDTH-2:0];

    // Final final result
    always @(posedge clkDS) begin
        out = rectifiedResult;
    end
endmodule

`endif