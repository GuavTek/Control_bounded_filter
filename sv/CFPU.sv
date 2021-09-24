`ifndef CFPU_SV_
`define CFPU_SV_

`include "Util.sv"

module CFPU #(parameter FPU_opcode op = ADD) (
    input complex A, B,
    output complex result
);

generate
    case (op)
        ADD:
        begin
            FPU #(.op(ADD)) fr1 (.A(A.r), .B(B.r), .result(result.r));
            FPU #(.op(ADD)) fi1 (.A(A.i), .B(B.i), .result(result.i));
        end
        MULT:
        begin
            //cmulcc.r = (a.r * b.r) - (a.i * b.i);
            //cmulcc.i = (a.i * b.r) + (a.r * b.i);
            complex i1, i2;
            floatType temp2;
            // Real result
            FPU #(.op(MULT)) fr1 (.A(A.r), .B(B.r), .result(i1.r));
            FPU #(.op(MULT)) fr2 (.A(A.i), .B(B.i), .result(temp2));
            assign i2.r.sign = !temp2.sign;
            assign i2.r.exp = temp2.exp;
            assign i2.r.mantis = temp2.mantis;
            FPU #(.op(ADD)) fr3 (.A(i1.r), .B(i2.r), .result(result.r));

            // Imaginary result
            FPU #(.op(MULT)) fi1 (.A(A.i), .B(B.r), .result(i1.i));
            FPU #(.op(MULT)) fi2 (.A(A.r), .B(B.i), .result(i2.i));
            FPU #(.op(ADD)) fi3 (.A(i1.i), .B(i2.i), .result(result.i));
        end
    endcase
endgenerate
endmodule

`endif