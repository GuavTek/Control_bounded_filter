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
            result = csubrc(0.0, factor);
        end
    end
endmodule