`ifndef FIXTOFIX_SV_
`define FIXTOFIX_SV_

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

    generate
        if (n_mant_out > n_mant_in)
            assign out = in <<< n_mant_out - n_mant_in;
        else
            assign out = in >>> n_mant_in - n_mant_out;
    endgenerate
    
endmodule

`endif