`ifndef FIXLUT_SV_
`define FIXLUT_SV_

`include "Util.sv"
`include "FixPU.sv"

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

    function automatic logic signed[n_tot:0] getVal(logic[size-1:0] in);
        logic signed[n_tot:0] temp = 0;
        int j;
        for(j = 0; j < size; j++) begin
            if(in[j] == 1) begin
                temp += fact[j][n_tot:0];
            end else begin
                temp -= fact[j][n_tot:0];
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

    localparam int AddersNum = $ceil((0.0 + size)/lut_size);
    localparam AdderLayers = $clog2(AddersNum);

    function automatic int GetAdderNum(int n);
        int temp = AddersNum;
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
        int temp = AddersNum;
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

    logic signed[n_tot:0] lutResults[AddersNum-1:0];
    logic signed[n_tot:0] adderResults[GetFirstReg(AdderLayers):0];
    // Generate LUTs
    generate

        for (genvar i = 0; i < AddersNum ; i++ ) begin : LUT_Gen
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

            if (lut_comb > 0) begin : Comb_Gen
                assign lutResults[i] = tempResult;
            end else begin : FF_Gen
                always @(posedge clk) begin
                    lutResults[i] = tempResult;
                end
            end
        end
    endgenerate

    // Generate adders
    generate
        genvar layer, ii;
        if (AdderLayers == 0) begin : No_Adders
            assign adderResults[0] = lutResults[0];
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
                        FixPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) adder_ (.A(lutResults[2*ii]), .B(lutResults[2*ii + 1]), .clk(clk), .result(tempResult));
                    end else begin : Reg_Gen
                        assign tempResult = lutResults[2*ii];
                    end
                end else begin : Layer_Gen
                    if ( ii < addfloor) begin : ADD_Gen
                        FixPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) adder_ (.A(adderResults[firstRes + 2*ii]), .B(adderResults[firstRes + 2*ii + 1]), .clk(clk), .result(tempResult));
                    end else begin : Reg_Gen
                        assign tempResult = adderResults[firstRes + 2*ii];
                    end
                end

                if ((i % adders_comb) > 0) begin : Comb_Gen
                    assign    adderResults[nextRes + ii] = tempResult;
                end else begin : FF_Gen
                    always @(posedge clk) begin
                        adderResults[nextRes + ii] = tempResult;
                    end
                end
                
            end
            
        end
    endgenerate

    assign result = adderResults[GetFirstReg(AdderLayers)];
endmodule

`endif
