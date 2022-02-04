`ifndef FIXLUT_SV_
`define FIXLUT_SV_

`include "Util.sv"
`include "FixPU.sv"

// Basic LUT
module FixLUT #(
    parameter   size = 1,
                n_int = 8,
                n_mant = 23,
    parameter logic signed[size-1:0][n_int+n_mant:0] fact = 'b0
    ) (
    sel,
    result
    );
    localparam n_tot = n_int + n_mant;
    input logic[size-1:0] sel;
    output logic signed[n_tot:0] result;
    logic signed[n_tot:0] mem[2**size-1:0];

    // Generates a sum of factors
    function automatic logic signed[n_tot:0] getVal(logic[size-1:0] in);
        logic signed[n_tot:0] temp = 0;
        int j;
        for(j = 0; j < size; j++) begin
            if(in[j] == 1) begin
                temp += fact[j];
            end else begin
                temp -= fact[j];
            end
        end
        return temp;
    endfunction

    // Generate LUT values
    generate
        for(genvar i = 0; i < 2**size; i++) begin
            localparam logic signed[n_tot:0] temp = getVal(i);
            assign mem[i] = temp;
        end
    endgenerate

    assign result = mem[sel];
endmodule

// A large LUT which gets broken down to smaller LUTs and summed
module FixLUT_Unit #(
    parameter   size = 1,
                lut_size = 6,
                n_int = 8,
                n_mant = 23,
                adders_comb = 0,
                lut_comb = 0,
    parameter logic signed[size-1:0][n_int+n_mant:0] fact = 0
) (
    sel,
    clk,
    result
);
    localparam n_tot = n_int + n_mant;
    input logic[size-1:0] sel;
    input logic clk;
    output logic signed[n_tot:0] result;

    localparam int LUTsNum = $ceil((0.0 + size)/lut_size);

    localparam int LUTRest = size % lut_size;
    function logic signed[lut_size-1:0][n_tot:0] GetFact (int startIndex);
        logic signed[lut_size-1:0][n_tot:0] tempArray;
            
        for (int i = 0; i < lut_size ; i++) begin
            tempArray[i] = fact[startIndex + i];
        end
        return tempArray;
    endfunction 

    function logic signed[LUTRest-1:0][n_tot:0] GetFactRest (int startIndex);
        logic signed[LUTRest-1:0][n_tot:0] tempArray;
            
        for (int i = 0; i < LUTRest ; i++) begin
            tempArray[i] = fact[startIndex + i];
        end
        return tempArray;
    endfunction

    logic signed[n_tot:0] lutResults[LUTsNum-1:0];
    
    generate
        // Generate LUTs
        for (genvar i = 0; i < LUTsNum ; i++ ) begin : LUT_Gen
            logic signed[n_tot:0] tempResult;
            localparam offset = i*lut_size;
            localparam lut_rem = size - offset;
            if (i < $floor(size/lut_size)) begin
                localparam logic signed[lut_size-1:0][n_tot:0] fact_slice = GetFact(offset);
                FixLUT #(.size(lut_size), .n_int(n_int), .n_mant(n_mant), .fact(fact_slice)) lut_f (.sel(sel[offset +: lut_size]), .result(tempResult));
            end else begin
                // Causes internal assertion error in synthesis tool?
                localparam logic signed[LUTRest-1:0][n_tot:0] fact_slice = GetFactRest(offset);
                FixLUT #(.size(LUTRest), .n_int(n_int), .n_mant(n_mant), .fact(fact_slice)) lut_r (.sel(sel[offset +: LUTRest]), .result(tempResult));
            end

            // Decide if LUT results should be combinatorial or registers
            if (lut_comb > 0) begin : Comb_Gen
                assign lutResults[i] = tempResult;
            end else begin : FF_Gen
                always @(posedge clk) begin
                    lutResults[i] = tempResult;
                end
            end
        end
    endgenerate

    // Sum the contribution of all LUTs
    FixSum #(.size(LUTsNum), .n_int(n_int), .n_mant(n_mant), .adders_comb(adders_comb)) sum1 (.in(lutResults), .clk(clk), .out(result));
endmodule

// A LUT where contributions are summed over several cycles
module FixLUT_Cumulative #(
    parameter   size = 1,
                lut_size = 6,
                n_int = 8,
                n_mant = 23,
                adders_comb = 0,
                lut_comb = 1,
    parameter logic signed[size-1:0][n_int+n_mant:0] fact = 0
    ) (
    sel,
    clk,
    sample,
    result
    );
    localparam n_tot = n_int + n_mant;
    input logic[size-1:0] sel;
    input logic clk, sample;
    output logic signed[n_tot:0] result;

    localparam int LUTsNum = $ceil((0.0 + size)/lut_size);
    localparam LUTPerStep = 2**adders_comb;
    localparam int StepsNum = $ceil((0.0 + LUTsNum)/LUTPerStep);
    localparam LUTLayers = $clog2(LUTsNum);
    localparam AdderLayers = (LUTLayers > adders_comb) ? adders_comb : LUTLayers;

    function automatic int GetAdderNum(int n);
        int temp = LUTPerStep;
        for(int i = 0; i < n; i++) begin
            //temp = $ceil(temp/2);
            temp += 1;
            temp >>= 1;
        end
        //temp = $floor(temp/2);
        temp >>= 1;
        GetAdderNum = temp;
    endfunction

    function automatic int GetRegsNum(int n);
        int temp = LUTPerStep;
        for (int i = 0; i <= n; i++) begin
            //temp = $ceil(temp/2);
            temp += 1;
            temp >>= 1;
        end
        GetRegsNum = temp;
    endfunction

    function automatic int GetFirstReg(int n);
        int temp = 0;
        for (int i = 1; i < n; i++)
            temp += GetRegsNum(i-1);
        GetFirstReg = temp;
    endfunction

    localparam LUTRest = size % lut_size;
    function logic signed[lut_size-1:0][n_tot:0] GetFact (int startIndex);
        logic signed[lut_size-1:0][n_tot:0] tempArray;
            
        for (int i = 0; i < lut_size ; i++) begin
            tempArray[i][n_tot:0] = fact[startIndex + i][n_tot:0];
        end
        return tempArray;
    endfunction

    function logic signed[LUTRest-1:0][n_tot:0] GetFactRest (int startIndex);
        logic signed[LUTRest-1:0][n_tot:0] tempArray;
            
        for (int i = 0; i < LUTRest ; i++) begin
            tempArray[i][n_tot:0] = fact[startIndex + i][n_tot:0];
        end
        return tempArray;
    endfunction

    logic signed[n_tot:0] lutResults[LUTsNum+LUTPerStep-1:0];
    logic signed[n_tot:0] adderResults[GetFirstReg(AdderLayers):0];
    // Generate LUTs
    generate

        for (genvar i = 0; i < LUTsNum ; i++ ) begin : LUT_Gen
            logic signed[n_tot:0] tempResult;
            localparam offset = i*lut_size;
            localparam lut_rem = size - offset;
            if (i < $floor(size/lut_size)) begin
                localparam logic signed[lut_size-1:0][n_tot:0] fact_slice = GetFact(offset);
                FixLUT #(.size(lut_size), .n_int(n_int), .n_mant(n_mant), .fact(fact_slice)) lut_ (.sel(sel[offset +: lut_size]), .result(tempResult));
            end else if (lut_rem > 0) begin
                localparam logic signed[lut_rem-1:0][n_tot:0] fact_slice = GetFactRest(offset);
                FixLUT #(.size(lut_rem), .n_int(n_int), .n_mant(n_mant), .fact(fact_slice)) lut_ (.sel(sel[offset +: lut_rem]), .result(tempResult));
            end

            if (lut_comb > 0) begin : Comb_Gen
                assign lutResults[i] = tempResult;
            end else begin : FF_Gen
                always @(posedge clk) begin
                    lutResults[i] <= tempResult;
                end
            end
        end
    endgenerate

    assign lutResults[LUTsNum +: LUTPerStep] = '{default: 0};


    // Generate adders
    logic signed[n_tot:0] lutSlice[LUTPerStep-1:0];
    generate
        genvar layer, ii;
        if (AdderLayers == 0) begin : No_Adders
            assign adderResults[0] = lutSlice[0];
        end
        
        for (layer = AdderLayers; layer > 0 ; layer-- ) begin : ADDER_Gen
            localparam i = layer - 1;
            localparam addfloor = GetAdderNum(i);
            localparam addceil = GetRegsNum(i);
            localparam firstRes = GetFirstReg(i);
            localparam nextRes = GetFirstReg(i+1);

            `ifdef VERBOSE_LVL
                if(`VERBOSE_LVL > 2)
                    $info("layer: %3d, addfloor: %4d, addceil: %4d, firstres: %4d, nextres: %4d", i, addfloor, addceil, firstRes, nextRes);
            `endif

            for ( ii = 0; ii < addceil; ii++) begin : Layer_Instance_Gen
                logic signed[n_tot:0] tempResult;
                if ( i == 0 ) begin : Core_Gen
                    if ( ii < addfloor ) begin : ADD_Gen
                        FixPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) adder_ (.A(lutSlice[2*ii]), .B(lutSlice[2*ii + 1]), .clk(clk), .result(tempResult));
                    end else begin : Reg_Gen
                        assign tempResult = lutSlice[2*ii];
                    end
                end else begin : Layer_Gen
                    if ( ii < addfloor) begin : ADD_Gen
                        FixPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) adder_ (.A(adderResults[firstRes + 2*ii]), .B(adderResults[firstRes + 2*ii + 1]), .clk(clk), .result(tempResult));
                    end else begin : Reg_Gen
                        assign tempResult = adderResults[firstRes + 2*ii];
                    end
                end

                assign    adderResults[nextRes + ii] = tempResult;
                
            end
            
        end
    endgenerate

    // Generate cumulative reg
    logic signed[n_tot:0] finRes;
    generate
        if (StepsNum > 1) begin
            logic negSample, posSample, rstPulse;
            always @(negedge clk) begin
                negSample = sample;
            end

            always @(posedge clk) begin
                posSample = sample;
            end

            assign rstPulse = sample && negSample && !posSample;

            logic[$clog2(StepsNum):0] step;
            logic cumDone, cumClk;
            always @(posedge cumClk, posedge rstPulse) begin
                if(rstPulse) begin
                    step = 0;
                end else begin
                    step++;
                end
            end

            assign cumDone = step == StepsNum;
            assign cumClk = clk || cumDone;

            assign lutSlice[LUTPerStep-1:0] = cumDone ? lutResults[LUTsNum +: LUTPerStep] : lutResults[step * LUTPerStep +: LUTPerStep];

            logic signed[n_tot:0] tempRes;
            FixPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) cumAdd (.A(adderResults[GetFirstReg(AdderLayers)]), .B(finRes), .clk(clk), .result(tempRes));

            always @(posedge clk) begin
                if (rstPulse) begin
                    finRes = 0;
                end else begin
                    finRes = tempRes;
                end
            end
        end else begin
            assign lutSlice[LUTPerStep-1:0] = lutResults[LUTPerStep-1:0];
            assign finRes = adderResults[GetFirstReg(AdderLayers)];
        end
    endgenerate
    
    always @(posedge sample) begin
        result = finRes;
    end
    
endmodule

`endif
