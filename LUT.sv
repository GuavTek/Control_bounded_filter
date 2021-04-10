function real calcLUT(int size, real fact[size-1:0], logic[size-1:0] in);
    real temp = 0.0;
    logic[size:0] j;
    for(j = 0; j < size; j++) begin
        if(in[j] == 1) begin
            temp += fact[j];
        end else begin
            temp -= fact[j];
        end
    end
    calcLUT = temp;
endfunction

module LUT #(
    parameter       size = 1,
    parameter real  re[0:size-1],
                    im[0:size-1]
) (
    input logic[size-1:0] sel,
    output complex result
);
    // Generate LUT values
    complex mem[2**size-1:0];

    genvar i;
    generate
        for(i = 0; i < size**2; i++) begin
            complex temp;
            assign temp.r = rtof(calcLUT(size, re, i));
            assign temp.i = rtof(calcLUT(size, im, i));
            assign mem[i] = temp;
        end
    endgenerate

    always_comb begin : select
        result = mem[sel];
    end
endmodule

