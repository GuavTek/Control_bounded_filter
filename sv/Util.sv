`ifndef _UTIL_SV_
`define _UTIL_SV_
// Misc utilities used in several modules

package FPU_p;
    typedef enum { 
        ADD = 0,
        MULT = 1
    } opcode;
endpackage

//package Float_p;
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

function automatic int GetFloatExpBias(int exp_bits);
    int floatBias;
    floatBias = 2 ** (exp_bits - 1) - 1;
    return floatBias;
endfunction
//endpackage


`endif  // _UTIL_SV_
