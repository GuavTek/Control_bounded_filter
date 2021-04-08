
module FPU #(FPU_opcode op) (
    input floatType A, B,
    output floatType result
);
    import Util::*;
    const int mant_width = $bits(floatType.mantis);
    const int prod_width = 2*mant_width-1;
    const int exp_width = $bits(floatType.exp);
    logic[prod_width:0] m1;
    logic[mant_width:0] s1, s2, s3, s4;
    logic[mant_width+1:0] r1;
    logic overflow, signX;
    logic[exp_width:0] signed shift, e1;

always begin
    signX = A.sign ^ B.sign;
    case (op)
    ADD:
    begin
        s1[mant_width-1:0] = A.mantis;
        s2[mant_width-1:0] = B.mantis;
        s1[mant_width] = 1;
        s2[mant_width] = 1;
        // Align
        if (A.exp > B.exp) begin
            shift = A.exp - B.exp;
            s4 = s2 >> shift;
            s3 = s1;
            e1 = A.exp;
        end 
        else if (A.exp < B.exp) begin
            shift = B.exp - A.exp;
            s3 = s1 >> shift;
            s4 = s2;
            e1 = B.exp;
        end
        else begin
            shift = 0;
            s3 = s1;
            s4 = s2;
            e1 = A.exp;
        end

        // Calculate mantissa
        if (signX) begin
            // Subtraction
            if (A.mantis < B.mantis) begin
                r1 = s4 - s3;
                result.sign = B.sign;
            end else begin
                r1 = s3 - s4;
                result.sign = A.sign;
            end
        end else begin
            // Addition
            result.sign = A.sign;
            r1 = s3 + s4;
        end     

        // Normalize mantissa
        if (r1[mant_width+1]) begin
            result.exp = e1 + 1;
            result.mantis = r1 >> 1;
        end else begin
            for (int i = 0; i <= mant_width; i++) begin
                if (r1[mant_width-i]) begin
                    result.exp = e1 - i;
                    result.mantis = r1 << i;
                    break;
                end
            end
        end

    end
    MULT:
    begin 
        // Calculate resulting sign
        result.sign = signX;
        
        // Calculate mantis
        m1 = A.mantis * B.mantis;
        overflow = m1[m_width];
        if (overflow)
            result.mantis = m1[prod_width:mant_width];
        else
            result.mantis = m1[prod_width-1:mant_width-1];

        //Calculate exponent
        result.exp = A.exp + B.exp + overflow;
    end
    default: 
    endcase
end

endmodule