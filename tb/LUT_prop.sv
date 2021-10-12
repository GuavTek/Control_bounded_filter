`include "../sv/LUT.sv"

`ifndef LUT_PROP_SV_
`define LUT_PROP_SV_

`ifndef VERBOSE_LVL
//    `define VERBOSE_LVL 0
`endif

module LUT_prop #(
    parameter       size = 1,
    parameter real  fact[0:size-1] = '{default: 0.0}
) (
    input logic[size-1:0] sel,
    input floatType result,
    input floatType mem[2**size-1:0]
);

    initial begin
        #100;
        for (int i = 0; i < 2**size ; i++ ) begin
            if (`VERBOSE_LVL > 1)
                $info("LUT value %d = %f", i, ftor(mem[i]));
        end
    end
endmodule

`endif