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
    // Generate LUT values
    logic signed[n_tot:0] mem[2**size-1:0];

    function automatic logic signed[n_tot:0] getVal(logic[size-1:0] in);
        logic signed[n_tot:0] temp = 0;
        logic[size:0] j;
        for(j = 0; j < size; j++) begin
            if(in[j] == 1) begin
                temp += fact[j][n_tot:0];
            end else begin
                temp -= fact[j][n_tot:0];
            end
        end
        return temp;
    endfunction

    genvar i;
    generate
        for(i = 0; i < 2**size; i++) begin
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
                is_comb = 0,
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

    localparam int AddersNum = $ceil(size/lut_size);
    localparam AdderLayers = $clog2(AddersNum);

    function int GetAdderNum(int n);
        automatic real temp = AddersNum;
        for(int i = 0; i < n; i++)
            temp = $ceil(temp/2);
        temp = $floor(temp/2);
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

    virtual class GetFact#(parameter slice_size = 1);
        static function logic signed[slice_size-1:0][n_tot:0] Get (int startIndex);
        logic signed[slice_size-1:0][n_tot:0] tempArray;
        
        for (int i = 0; i < slice_size ; i++) begin
            tempArray[i][n_tot:0] = fact[startIndex + i][n_tot:0];
        end
        return tempArray;
    endfunction 
    endclass

    logic signed[n_tot:0] lutResults[AddersNum-1:0];
    logic signed[n_tot:0] adderResults[GetFirstReg(AdderLayers):0];
    // Generate LUTs
    generate
        localparam LUTRest = size % lut_size;

        for (genvar i = 0; i < AddersNum ; i++ ) begin : LUT_Gen
            localparam offset = i*lut_size;
            localparam lut_rem = size - offset;
            if (i < $floor(size/lut_size)) begin
                localparam logic signed[lut_size-1:0][n_tot:0] fact_slice = GetFact#(lut_size)::Get(offset);
                FixLUT #(.size(lut_size), .n_int(n_int), .n_mant(n_mant), .fact(fact_slice)) lut_ (.sel(sel[offset +: lut_size]), .result(lutResults[i]));
            end else if (lut_rem > 0) begin
                localparam logic signed[lut_rem-1:0][n_tot:0] fact_slice = GetFact#(lut_rem)::Get(offset);
                FixLUT #(.size(lut_rem), .n_int(n_int), .n_mant(n_mant), .fact(fact_slice)) lut_ (.sel(sel[offset +: lut_rem]), .result(lutResults[i]));
            end
        end
    endgenerate

    // Generate adders
    generate
        genvar i, ii;
        for (i = 0; i < AdderLayers ; i++ ) begin
            localparam addfloor = GetAdderNum(i);
            localparam addceil = GetRegsNum(i);
            localparam firstRes = GetFirstReg(i);
            localparam nextRes = GetFirstReg(i+1);

            for ( ii = 0; ii < addceil; ii++) begin
                logic signed[n_tot:0] tempResult;
                if ( i == 0 ) begin
                    if ( ii < addfloor ) begin
                        FixPU #(.op(ADD), .n_int(n_int), .n_mant(n_mant)) adder_ (.A(lutResults[2*ii]), .B(lutResults[2*ii + 1]), .clk(clk), .result(tempResult));
                    end else begin
                        assign tempResult = lutResults[2*ii];
                    end
                end else begin
                    if ( ii < addfloor) begin
                        FixPU #(.op(ADD), .n_int(n_int), .n_mant(n_mant)) adder_ (.A(adderResults[firstRes + 2*ii]), .B(adderResults[firstRes + 2*ii + 1]), .clk(clk), .result(tempResult));
                    end else begin
                        assign tempResult = adderResults[firstRes + 2*ii];
                    end
                end

                if (is_comb > 0) begin
                    assign    adderResults[nextRes + ii] = tempResult;
                end else begin
                    always @(posedge clkDS) begin
                        adderResults[nextRes + ii] = tempResult;
                    end
                end
                
            end
            
        end
    endgenerate

    assign result = adderResults[GetFirstReg(AdderLayers)];
endmodule

`endif
