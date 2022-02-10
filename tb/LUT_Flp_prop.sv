`ifndef LUT_FLP_PROP_SV_
`define LUT_FLP_PROP_SV_

`include "../sv/LUT_Flp.sv"
`include "Util_TB.sv"

module LUT_Flp_prop #(
    parameter       size = 1, n_mant = 48, n_int = 15, f_exp = 8, f_mant = 23,
    parameter logic signed[size-1:0][n_mant+n_int:0] fact = '{default: 0},
    type float_t = struct {logic sign; logic[7:0] exp; logic[23:0] mant;}
) (
    input logic[size-1:0] sel,
    input float_t result,
    input float_t mem[2**size-1:0]
);

    initial begin
        #100;
        for (int i = 0; i < 2**size ; i++ ) begin
            if (`VERBOSE_LVL > 3)
                $info("LUT value %d = %f", i, convert_nonsynth #(.f_exp(f_exp), .f_mant(f_mant))::ftor(mem[i]));
        end
    end
endmodule

`endif