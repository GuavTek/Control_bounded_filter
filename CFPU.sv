`include "FPU.sv"
module FPU #() (
    in complex A, B,
    in FPU_opcode op,
    out complex result
);

generate
    case (op)
        ADD:
        begin
            FPU fr1 (.A(A.r), .B(B.r), .op(ADD), .result(result.r));
            FPU fi1 (.A(A.i), .B(B.i), .op(ADD), .result(result.i));
        end
        MULT:
        begin
            //cmulcc.r = (a.r * b.r) - (a.i * b.i);
            //cmulcc.i = (a.i * b.r) + (a.r * b.i);
            complex i1, i2;
            floatType temp2;
            // Real result
            FPU fr1 (.A(A.r), .B(B.r), .op(MULT), .result(i1.r));
            FPU fr2 (.A(A.i), .B(B.i), .op(MULT), .result(temp2));
            assign i2.r.sign = !temp2.sign;
            assign i2.r.exp = temp2.exp;
            assign i2.r.mantis = temp2.mantis;
            FPU fr3 (.A(i1.r), .B(i3.r), .op(ADD), .result(result.r));

            // Imaginary result
            FPU fi1 (.A(A.i), .B(B.r), .op(MULT), .result(i1.i));
            FPU fi2 (.A(A.r), .B(B.i), .op(MULT), .result(i2.i));
            FPU fi3 (.A(i1.i), .B(i2.i), .op(ADD), .result(result.i));
        end
        default: 
    endcase
endgenerate
endmodule