
module LUT #(
    parameter   re = 0.0,
                im = 0.0
) (
    input logic sel,
    output complex result
);
    complex factorP, factorN;
    assign factorP.r = rtof(re);
    assign factorP.i = rtof(im);
    assign factorN.r = rtof(-re);
    assign factorN.i = rtof(-im);

    always_comb begin : select
        if (sel)
            result = factorP;
        else begin
            result = factorN;
        end
    end
endmodule