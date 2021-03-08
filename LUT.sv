`include "ComplexType.sv"

module LUT #(
    parameter   re = 0.0,
                im = 0.0
) (
    input logic sel,
    output complex result
);
    complex factor;
    factor.r = re;
    factor.i = im;


    always_comb begin : select
        if (sel)
            result = factor;
        else begin
            result = csubrc(0.0, factor);
        end
    end
endmodule