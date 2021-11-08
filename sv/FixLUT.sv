`ifndef FIXLUT_SV_
`define FIXLUT_SV_

`include "Util.sv"

module FixLUT #(
    parameter   size = 1,
                n_int = 8,
                n_mant = 23,
    parameter logic signed[size-1:0][n_int+n_mant:0] fact = 'b0
) (
    sel,
    result
);
    localparam n_tot = n_int + n_mant;
    input logic[size-1:0] sel;
    output logic signed[n_tot:0] result;
    // Generate LUT values
    logic signed[n_tot:0] mem[2**size-1:0];

    function automatic logic signed[n_tot:0] getVal(logic[size-1:0] in);
        logic signed[n_tot:0] temp = 0;
        logic[size:0] j;
        for(j = 0; j < size; j++) begin
            if(in[j] == 1) begin
                temp += fact[j][n_tot:0];
            end else begin
                temp -= fact[j][n_tot:0];
            end
        end
        return temp;
    endfunction

    genvar i;
    generate
        for(i = 0; i < 2**size; i++) begin
            localparam logic signed[n_tot:0] temp = getVal(i);
            assign mem[i] = temp;
        end
    endgenerate

    
    assign result = mem[sel];
endmodule

`endif
