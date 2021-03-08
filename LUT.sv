
module LUT #(
    parameter   re = 0.0,
                im = 0.0
) (
    input logic sel,
    output complex result
);
    complex factor;
    
    always_comb begin : select
        factor.r = re;
        factor.i = im;
        if (sel)
            result = factor;
        else begin
            result = csubrc(0.0, factor);
        end
    end
endmodule