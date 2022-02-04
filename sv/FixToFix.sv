`ifndef FIXTOFIX_SV_
`define FIXTOFIX_SV_

// A module to convert between fixed-point formats
module FixToFix #(
    parameter   n_int_in = 8, n_mant_in = 23,
                n_int_out = 8, n_mant_out = 23
) (
    in, out
);
    localparam n_tot_in = n_int_in + n_mant_in;
    localparam n_tot_out = n_int_out + n_mant_out;
    input logic signed[n_tot_in:0] in;
    output logic signed[n_tot_out:0] out;
    logic[n_tot_out+1:0] temp;

    generate
        if (n_mant_out > n_mant_in)
            assign temp = (in <<< n_mant_out - n_mant_in +1);
        else
            assign temp = (in >>> n_mant_in - n_mant_out -1) + 1;
    endgenerate
    
    assign out = temp[n_tot_out+1:1];

endmodule

`endif