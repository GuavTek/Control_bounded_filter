`ifndef _UTIL_SV_
`define _UTIL_SV_
// Misc utilities used in several modules

package FPU_p;
    typedef enum { 
        ADD = 0,
        MULT = 1
    } opcode;
endpackage

// Functions to slice and resize ADC constants
virtual class GetConst #(parameter n_int = 8, n_mant = 23, size = 10);
    
    static function logic signed[size-1:0][n_int+n_mant:0] Hb ();
        import Coefficients_Fx::COEFF_BIAS;
        import Coefficients_Fx::hb;
        logic signed[size-1:0][n_int+n_mant:0] tempArray;

        for (int i = 0; i < size ; i++) begin
            logic signed[n_int+n_mant:0] temp = hb[i] >>> (COEFF_BIAS - n_mant);
            tempArray[i][n_int+n_mant:0] = temp;
        end
        return tempArray;
    endfunction

    static function logic signed[size-1:0][n_int+n_mant:0] Hf ();
        import Coefficients_Fx::COEFF_BIAS;
        import Coefficients_Fx::hf;
        logic signed[size-1:0][n_int+n_mant:0] tempArray;
        
        for (int i = 0; i < size ; i++) begin
            logic signed[n_int+n_mant:0] temp = hf[i] >>> (COEFF_BIAS - n_mant);
            tempArray[i] = temp;
        end
        return tempArray;
    endfunction

    static function logic signed[size-1:0][n_int+n_mant:0] Fbr (int row);
        import Coefficients_Fx::COEFF_BIAS;
        logic signed[size-1:0][n_int+n_mant:0] tempArray;

        for (int i = 0; i < size ; i++) begin
            tempArray[i] = Coefficients_Fx::Fbr[row][i] >>> (COEFF_BIAS - n_mant);
        end
        return tempArray;
    endfunction

    static function logic signed[size-1:0][n_int+n_mant:0] Fbi (int row);
        import Coefficients_Fx::COEFF_BIAS;
        logic signed[size-1:0][n_int+n_mant:0] tempArray;

        for (int i = 0; i < size ; i++) begin
            tempArray[i] = Coefficients_Fx::Fbi[row][i] >>> (COEFF_BIAS - n_mant);
        end
        return tempArray;
    endfunction

    static function logic signed[size-1:0][n_int+n_mant:0] Ffr (int row);
        import Coefficients_Fx::COEFF_BIAS;
        logic signed[size-1:0][n_int+n_mant:0] tempArray;

        for (int i = 0; i < size ; i++) begin
            tempArray[i] = Coefficients_Fx::Ffr[row][i] >>> (COEFF_BIAS - n_mant);
        end
        return tempArray;
    endfunction

    static function logic signed[size-1:0][n_int+n_mant:0] Ffi (int row);
        import Coefficients_Fx::COEFF_BIAS;
        logic signed[size-1:0][n_int+n_mant:0] tempArray;

        for (int i = 0; i < size ; i++) begin
            tempArray[i] = Coefficients_Fx::Ffi[row][i] >>> (COEFF_BIAS - n_mant);
        end
        return tempArray;
    endfunction

    static function logic signed[n_int+n_mant:0] Wfr(int row);
        import Coefficients_Fx::COEFF_BIAS;

        return Coefficients_Fx::Wfr[row] >>> (COEFF_BIAS - n_mant);
    endfunction

    static function logic signed[n_int+n_mant:0] Wfi(int row);
        import Coefficients_Fx::COEFF_BIAS;

        return Coefficients_Fx::Wfi[row] >>> (COEFF_BIAS - n_mant);
    endfunction

    static function logic signed[n_int+n_mant:0] Wbr(int row);
        import Coefficients_Fx::COEFF_BIAS;

        return Coefficients_Fx::Wbr[row] >>> (COEFF_BIAS - n_mant);
    endfunction

    static function logic signed[n_int+n_mant:0] Wbi(int row);
        import Coefficients_Fx::COEFF_BIAS;

        return Coefficients_Fx::Wbi[row] >>> (COEFF_BIAS - n_mant);
    endfunction

    static function logic signed[1:0][n_int+n_mant:0] cpow(logic signed[63:0] r, logic signed[63:0] i, int exp);
        import Coefficients_Fx::COEFF_BIAS;
        logic signed[1:0][n_int+n_mant:0] result;
        logic signed[63:0] tempR, tempI;
        tempR = r;
        tempI = i;

        for (int j = 1; j < exp ; j++ ) begin
            //cmulcc.r = (a.r * b.r) - (a.i * b.i);
            //cmulcc.i = (a.i * b.r) + (a.r * b.i);
            logic signed[127:0] tempReal, tempImag;
            tempReal = (tempR * r) - (tempI * i);
            tempImag = (tempI * r) + (tempR * i);
            tempR = tempReal >>> COEFF_BIAS;
            tempI = tempImag >>> COEFF_BIAS;
        end
        result[0][n_int+n_mant:0] = tempR >>> (COEFF_BIAS - n_mant);
        result[1][n_int+n_mant:0] = tempI >>> (COEFF_BIAS - n_mant);
        return result;
    endfunction
endclass //GetConst

// Functions to convert between fixed-point and floating-point
virtual class convert #(parameter n_int = 8, n_mant = 23, f_exp = 8, f_mant = 23);
    static function logic[f_mant+f_exp:0] itof(logic signed[n_int+n_mant:0] in);
        logic[f_mant+f_exp:0] temp;
        int signed exponent;
        int signed mant_shift;
        logic[f_mant+n_mant:0] temp_mant;
        logic signed[n_int+n_mant:0] absIn;
        logic signed[n_int+n_mant:0] tempClog;
        int countClog = 0;
        int floatBias = 2 ** (f_exp - 1) - 1;

        if (in == 0) begin
            temp[f_mant+f_exp] = 0; // Sign
            exponent = -floatBias;
            absIn = 0;
        end else begin    
            if (in < 0) begin
                absIn = -in;
                temp[f_mant+f_exp] = 1; // Sign
            end else begin
                absIn = in;
                temp[f_mant+f_exp] = 0; // Sign
            end
                
            tempClog = absIn;

            for (countClog = 0; tempClog > 0 ; countClog++) begin
                tempClog >>= 1;
            end

            exponent = countClog - n_mant - 1;
        end
        //$display("absIn = %h", absIn);
        //$display("exponent = %3d - %2d - 1 = %3d", $clog2(absIn + 1), n_mant, exponent);
                
        // Clamp exponent for subnormal numbers
        if (-exponent > floatBias) begin
            mant_shift = -floatBias + n_mant - f_mant;
            temp[f_mant +: f_exp] = 0; // Exponent
        end else begin
            mant_shift = n_mant - f_mant + exponent;
            temp[f_mant +: f_exp] = exponent + floatBias; // Exponent
        end

        if (mant_shift < 0) begin
            temp_mant = absIn << -mant_shift;
        end else begin
            temp_mant = absIn >> mant_shift;
        end

        //$display("temp_mant = %h >> %3d = %h", absIn, mant_shift, temp_mant);

        temp[0 +: f_mant] = temp_mant;

        return temp;
    endfunction //itof()
        
    //function logic signed[n_int+n_mant:0] ftoi(float_t in);
            
    //endfunction //ftoi()
    
endclass //convert

// Returns the exponent bias given the number of bits
function automatic int GetFloatExpBias(int exp_bits);
    int floatBias;
    floatBias = 2 ** (exp_bits - 1) - 1;
    return floatBias;
endfunction

`endif  // _UTIL_SV_
