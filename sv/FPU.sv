`include "HardFloat-1/source/fNToRecFN.v"
`include "HardFloat-1/source/recFNToFN.v"
`include "HardFloat-1/source/addRecFN.v"
`include "HardFloat-1/source/mulRecFN.v"
`include "HardFloat-1/source/HardFloat_consts.vi"
`include "Util.sv"

module FPU #(parameter FPU_opcode op) (
    input floatType A, B,
    output floatType result
);
    const int mant_width = $bits(result.mantis);
    const int exp_width = $bits(result.exp);
    logic[(mant_width + exp_width):0] s1, s2, r1;

    fNToRecFN #(.expWidth(exp_width), .sigWidth(mant_width+1)) aConv (.in(A), .out(s1));
    fNToRecFN #(.expWidth(exp_width), .sigWidth(mant_width+1)) bConv (.in(B), .out(s2));
    recFNToFN #(.expWidth(exp_width), .sigWidth(mant_width+1)) resConv (.in(r1), .out(result));

    generate
        case (op)
        ADD:
        begin
            addRecFN #(.expWidth(exp_width), .sigWidth(mant_width+1)) add1 (.control(flControl_tininessAfterRounding), .subOp(0), .a(s1), .b(s2), .roundingMode(round_near_even), .out(r1));
        end
        MULT:
        begin 
            mulRecFN #(.expWidth(exp_width), .sigWidth(mant_width+1)) mul1 (.control(1), .a(s1), .b(s2), .roundingMode(round_near_even), .out(r1));
        end
        endcase
    endgenerate

endmodule