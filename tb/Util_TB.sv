`ifndef _UTIL_TB_SV_
`define _UTIL_TB_SV_
// Misc utilities which are not synthesizable

// Make a string from the contents of a define
`define STRINGIFY(x) $sformatf("%0s", `"x`")

// Conversions between float format and the "real" datatype 
virtual class convert_nonsynth #(parameter n_int = 8, n_mant = 23, f_exp = 8, f_mant = 23);
    static function int signed flog2(real in);
        if(in <= 0) begin
            $error("Logarithm of 0 or less is not attainable");
            flog2 = 0;
        end else begin
            int signed temp = 0;
            if (in >= 1)
                while(in > 1) begin
                    in = in / 2;
                    if (in >= 1) temp++;
                end
            else
                while(in < 1) begin
                    in = in * 2;
                    temp--;
                end
            flog2 = temp;
        end
    endfunction

    static function real ftor(logic[f_exp+f_mant:0] in);
        real tempR;    
        logic[f_mant:0] tempF;
        real floatBias = 2 ** (f_exp - 1) - 1;
        real bias = real'(in[f_mant +: f_exp]) - floatBias - real'(f_mant);

        if(in[f_mant +: f_exp] > 0)
            tempF = {1'b1, in[0 +: f_mant]};
        else
            tempF = {1'b0, in[0 +: f_mant]};
            
        if (in[f_exp+f_mant]) begin
            tempR = -real'(tempF);
        end else begin
            tempR = real'(tempF);
        end
        tempR = tempR * 2.0**(bias);

        ftor = tempR;
    endfunction

    static function logic[f_exp+f_mant:0] rtof(real in);
        logic[f_exp+f_mant:0] temp;
        int floatBias;
        real absIn;
        logic[f_exp:0] mant;
        int signed exponent;
        floatBias = 2 ** (f_exp - 1) - 1;
                
        if (in == 0) begin
            temp[f_exp+f_mant] = 0;
            exponent = -floatBias;
            absIn = 0;
        end else if (in > 0) begin
            temp[f_exp+f_mant] = 0;
            exponent = flog2(in);
            absIn = in;
        end else begin
            temp[f_exp+f_mant] = 1;
            exponent = flog2(-in);
            absIn = -in;
        end

        // Prevent underflow for subnormal values
        if ((exponent + floatBias) < 0) begin
            exponent = -floatBias;
        end
                
        temp[f_mant +: f_exp] = exponent + floatBias;
        mant = (absIn * 2.0**(f_exp-exponent));
        temp[0 +: f_mant] = mant[f_exp-1:0];
        return temp;
    endfunction
    /**/
endclass //convert

// Return the absolute value of real
function automatic real absr(real in);
    if(in >= 0)
        absr = in;
    else
        absr = -in;
endfunction

`endif  // _UTIL_SV_
