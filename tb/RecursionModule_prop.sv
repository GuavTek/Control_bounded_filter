`ifndef RECURSIONMODULE_PROP_SV_
`define RECURSIONMODULE_PROP_SV_

`include "../sv/RecursionModule.sv"
`include "../sv/Util.sv"

// How much results can vary due to precision differences
`define F_SLACK 0.001

module RecursionModule_prop #(
    parameter floatType factorR = rtof(0.0),
                factorI = rtof(0.0)
) (
    input complex in,
    input complex resetVal,
    input logic rst, clk,
    input complex out,
    input complex prev, factor
);
    
    assert property (@(posedge clk) absr(ftor(out.r) - (ftor(prev.r) * ftor(factor.r) - ftor(prev.i) * ftor(factor.i) + ftor(in.r))) < `F_SLACK*absr(ftor(out.r)) )
    else $warning("Wrong real value!! %f out, but should be %f", ftor(out.r), (ftor(prev.r) * ftor(factor.r) - ftor(prev.i) * ftor(factor.i) + ftor(in.r)));

    assert property (@(posedge clk) absr(ftor(out.i) - (ftor(prev.r) * ftor(factor.i) + ftor(prev.i) * ftor(factor.r) + ftor(in.i))) < `F_SLACK*absr(ftor(out.i)) )
    else $warning("Wrong imag value!! %f out, but should be %f", ftor(out.i), (ftor(prev.r) * ftor(factor.i) + ftor(prev.i) * ftor(factor.r) + ftor(in.i)));

endmodule
`endif
