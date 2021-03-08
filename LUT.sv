module LUT #(
    complex factor
) (
    input logic sel,
    output complex result
);
    
    always_comb begin : select
        if (sel)
            result = factor;
        else
            result = 0-factor;
    end
endmodule