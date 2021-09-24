`ifndef FPU_SV_
`define FPU_SV_

`include "HardFloat-1/source/HardFloat_consts.vi"
`include "HardFloat-1/source/HardFloat_primitives.v"
`include "HardFloat-1/source/isSigNaNRecFN.v"
`include "HardFloat-1/source/HardFloat_rawFN.v"
`include "HardFloat-1/source/fNToRecFN.v"
`include "HardFloat-1/source/recFNToFN.v"
`include "HardFloat-1/source/addRecFN.v"
`include "HardFloat-1/source/mulRecFN.v"
`include "Util.sv"

module FPU #(parameter FPU_opcode op = ADD) (
    input floatType A, B,
    output floatType result
);
    logic clk;  // dummy for property checker
    logic[(`MANT_W + `EXP_W + 1):0] s1, s2, r1;

    fNToRecFN #(.expWidth(`EXP_W), .sigWidth(`MANT_W+1)) aConv (.in(A), .out(s1));
    fNToRecFN #(.expWidth(`EXP_W), .sigWidth(`MANT_W+1)) bConv (.in(B), .out(s2));
    recFNToFN #(.expWidth(`EXP_W), .sigWidth(`MANT_W+1)) resConv (.in(r1), .out(result));

    generate
        case (op)
        ADD:
        begin
            logic[4:0] dummy;
            addRecFN #(.expWidth(`EXP_W), .sigWidth(`MANT_W+1)) add1 (.control(`flControl_tininessAfterRounding), .subOp(1'b0), .a(s1), .b(s2), .roundingMode(`round_near_even), .out(r1), .exceptionFlags(dummy));
        end
        MULT:
        begin 
            logic[4:0] dummy;
            mulRecFN #(.expWidth(`EXP_W), .sigWidth(`MANT_W+1)) mul1 (.control(`flControl_tininessAfterRounding), .a(s1), .b(s2), .roundingMode(`round_near_even), .out(r1), .exceptionFlags(dummy));
        end
        endcase
    endgenerate

endmodule

`endif