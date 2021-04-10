
module LUT #(
    parameter       size = 1,
    parameter real  re[size-1:0],
                    im[size-1:0]
) (
    input logic[size-1:0] sel,
    output complex result
);
    // Generate LUT values
    complex mem[2**size-1:0];
    genvar i;
    genvar j;
    generate
        for(i = 0; i < size**2; i++) begin
            genvar tempR = 0.0;
            benvar tempI = 0.0;
            for(j = 0; j < size; j++) begin
                if(i[j] == 1) begin
                    tempR += re[j];
                    tempI += im[j];
                end else begin
                    tempR -= re[j];
                    tempI -= im[j];
                end
            end
            mem[i].r = rtof(tempR);
            mem[i].i = rtof(tempI);
        end
    endgenerate

    always_comb begin : select
        result = mem[sel];
    end
endmodule