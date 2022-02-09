`ifndef LUT_SV_
`define LUT_SV_

`include "Util.sv"

module LUT #(
    parameter       size = 1, n_mant = 48, n_int = 15, f_exp = 8, f_mant = 23,
    parameter logic signed[size-1:0][n_mant+n_int:0] fact = '{default: 0},
    type float_t = struct {logic sign; logic[7:0] exp; logic[23:0] mant;}
) (
    input logic[size-1:0] sel,
    output float_t result
);
    float_t mem[2**size-1:0];

    function automatic logic signed[n_mant+n_int:0] getVal(logic[size-1:0] in);
        logic signed[n_mant+n_int:0] temp = 0;
        logic[size:0] j;
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
            localparam logic signed[n_mant+n_int:0] temp = getVal(i);
            ConvertITOF #(.n_int(n_int), .n_mant(n_mant), .f_exp(f_exp), .f_mant(f_mant), .in(temp)) itof ();
            //$info("%f was converted to %h", ($itor(getVal(i))) / n_mant, temp);
            assign mem[i] = itof.result;
        end
    endgenerate

    assign result = mem[sel];
endmodule

module LUT_Unit #(
    parameter   size = 1,
                lut_size = 6,
                n_int = 15,
                n_mant = 48,
                f_exp = 8,
                f_mant = 23,
                adders_comb = 0,
                lut_comb = 0,
    parameter logic signed[size-1:0][n_int+n_mant:0] fact = 0,
    type float_t = struct {logic sign; logic[7:0] exp; logic[22:0] mant;}
) (
    sel,
    clk,
    result
);
    localparam n_tot = n_int + n_mant;
    input logic[size-1:0] sel;
    input logic clk;
    output float_t result;

    localparam int LUTsNum = $ceil((0.0 + size)/lut_size);

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

    float_t lutResults[LUTsNum-1:0];

    generate
        // Generate LUTs
        for (genvar i = 0; i < LUTsNum ; i++ ) begin : LUT_Gen
            float_t tempResult;
            localparam offset = i*lut_size;
            localparam lut_rem = size - offset;
            if (i < $floor(size/lut_size)) begin
                localparam logic signed[lut_size-1:0][n_tot:0] fact_slice = GetFact(offset);
                LUT #(.size(lut_size), .n_int(n_int), .n_mant(n_mant), .f_exp(f_exp), .f_mant(f_mant), .fact(fact_slice), .float_t(float_t)) lut_ (.sel(sel[offset +: lut_size]), .result(tempResult));
            end else if (lut_rem > 0) begin
                localparam logic signed[lut_rem-1:0][n_tot:0] fact_slice = GetFactRest(offset);
                LUT #(.size(lut_rem), .n_int(n_int), .n_mant(n_mant), .f_exp(f_exp), .f_mant(f_mant), .fact(fact_slice), .float_t(float_t)) lut_ (.sel(sel[offset +: lut_rem]), .result(tempResult));
            end

            // Decide if LUT results should be combinatorial or registers
            if (lut_comb > 0) begin : Comb_Gen
                assign lutResults[i] = tempResult;
            end else begin : FF_Gen
                always @(posedge clk) begin
                    lutResults[i] <= tempResult;
                end
            end
        end
    endgenerate

    // Sum the contribution of all LUTs
    FloatSum #(.size(LUTsNum), .f_exp(f_exp), .f_mant(f_mant), .adders_comb(adders_comb), .float_t(float_t)) sum1 (.in(lutResults), .clk(clk), .out(result));
endmodule

`endif
