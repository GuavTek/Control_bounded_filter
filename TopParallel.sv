`include "Util.sv"
`include "RecursionModule.sv"
`include "LUT.vhd"

module Parallel_top #(
    parameter stages = 32,
    parameter width = 16,
    parameter N = 3
) (
    input logic [N-1:0] in,
    output logic [width-1:0] out
);
    
endmodule