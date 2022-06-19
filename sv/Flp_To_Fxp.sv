`ifndef FLPTOFXP_SV_
`define FLPTOFXP_SV_

`include "Util.sv"

// A synthesizable module which converts from floating point to fixed point
module Flp_To_Fxp #(
    parameter   n_int_out = 8, n_mant_out = 23, n_exp_in = 8, n_mant_in = 23,
    type float_t = struct {logic sign; logic[7:0] exp; logic[23:0] mant;}
) (
    in, out
);
    localparam n_tot_out = n_int_out + n_mant_out;
    input float_t in;
    output logic signed[n_tot_out:0] out;
    logic[n_tot_out+1:0] temp;

    localparam n_tot_in = n_exp_in + n_mant_in;
    localparam expBias = GetFloatExpBias(n_exp_in);

    logic[n_mant_in:0] num_in;
    assign num_in = (in.exp == 0) ? {1'b0, in.mant} : {1'b1, in.mant};

    logic signed[n_tot_out:0] num_signed;
    assign num_signed = in.sign ? -temp[n_tot_out+1:1] : temp[n_tot_out+1:1];

    logic signed[n_exp_in:0] exponent;
    assign exponent = in.exp - expBias;

    logic signed[n_exp_in+1:0] shift;
    assign shift = n_mant_in - n_mant_out - exponent - 1;

    assign temp = ((shift < 0) ? num_in << -shift : num_in >> shift) + 1;

    assign out = num_signed;

endmodule

`endif
