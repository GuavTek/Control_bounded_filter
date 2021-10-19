`ifndef LUT_SV_
`define LUT_SV_

`include "Util.sv"

module LUT #(
    parameter       size = 1,
    parameter floatType[0:size-1] fact = '{default: rtof(0.0)}
) (
    input logic[size-1:0] sel,
    output floatType result
);
    // Generate LUT values
    floatType mem[2**size-1:0];

    function automatic real getVal(logic[size-1:0] in);
        automatic real temp = 0.0;
        logic[size:0] j;
        for(j = 0; j < size; j++) begin
            if(in[j] == 1) begin
                temp += ftor(fact[j]);
            end else begin
                temp -= ftor(fact[j]);
            end
        end
        getVal = temp;
    endfunction

    genvar i;
    generate
        for(i = 0; i < 2**size; i++) begin
            assign mem[i] = rtof(getVal(i));
        end
    endgenerate

    always_comb begin : select
        result = mem[sel];
    end
endmodule

`endif
