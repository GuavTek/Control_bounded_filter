module LUT #(
    complex factor
) (
    input logic sel,
    output complex result
);
    
    always_comb begin : select
        if (sel)
            result = factor;
        else begin
            result.r = -factor.r;
            result.i = -factor.i;
        end
    end
endmodule