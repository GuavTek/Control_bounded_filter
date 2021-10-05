`include "../sv/LUT.sv"

`ifndef LUT_PROP_SV_
`define LUT_PROP_SV_

`ifndef VERBOSE_LVL
//    `define VERBOSE_LVL 0
`endif

module LUT_prop #(
    parameter       size = 1,
    parameter real  re[0:size-1] = '{default: 0.0},
    parameter real  im[0:size-1] = '{default: 0.0}
) (
    input logic[size-1:0] sel,
    input complex result,
    input complex mem[2**size-1:0]
);

    initial begin
        #100;
        for (int i = 0; i < 2**size ; i++ ) begin
            if (`VERBOSE_LVL > 1)
                $info("LUT value %d - r=%f \t i=%f", i, ftor(mem[i].r), ftor(mem[i].i));
        end
    end
endmodule

`endif