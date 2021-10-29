`ifndef _UTIL_SV_
`define _UTIL_SV_
// Misc utilities used in several modules

`define STRINGIFY(x) $sformatf("%0s", `"x`")

typedef enum int { 
    ADD = 0,
    MULT = 1
} FPU_opcode;

// Floored log2
function int signed flog2(real in);
    begin
    if(in <= 0) begin
        $error("Logarithm of 0 or less is not attainable");
        flog2 = 0;
    end else begin
        automatic int signed temp = 0;
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
	end
endfunction

//package float_p;
    `ifndef EXP_W
        `define EXP_W 5
    `endif  // EXP_W
    `ifndef MANT_W
        `define MANT_W 11
    `endif  // MANT_W

    typedef struct packed { 
        logic sign; 
        logic[`EXP_W-1:0] exp;
        logic[`MANT_W-1:0] mantis;
    } floatType;

    typedef struct packed {
        floatType r;
        floatType i;
    } complex;

    function floatType rtof(real in);
        begin
        floatType temp;
        int floatBias;
        real absIn;
        logic[`MANT_W:0] mant;
        automatic int signed exponent;
        floatBias = 2 ** (`EXP_W - 1) - 1;
            
        if (in == 0) begin
            temp.sign = 0;
            exponent = -floatBias;
            absIn = 0;
        end else if (in > 0) begin
            temp.sign = 0;
            exponent = flog2(in);
            absIn = in;
        end else begin
            temp.sign = 1;
            exponent = flog2(-in);
            absIn = -in;
        end
            
        // Prevent underflow for subnormal values
        if ((exponent + floatBias) < 0) begin
            exponent = -floatBias;
        end
            
        temp.exp = exponent + floatBias;
        mant = (absIn * 2.0**(`MANT_W-exponent));
        temp.mantis = mant[`MANT_W-1:0];
        rtof = temp;
        end
    endfunction

    function real ftor(floatType in);
        begin
        real tempR;    
        logic[`MANT_W:0] tempF;
        automatic real floatBias = 2 ** (`EXP_W - 1) - 1;
        automatic real bias = real'(in.exp) - floatBias - real'(`MANT_W);

        if(in.exp > 0)
        tempF = {1'b1, in.mantis};
        else
            tempF = {1'b0, in.mantis};
        
        if (in.sign) begin
            tempR = -real'(tempF);
        end else begin
            tempR = real'(tempF);
        end
        tempR = tempR * 2.0**(bias);

        ftor = tempR;
        end
    endfunction

    function real absr(real in);
        if(in >= 0)
            absr = in;
        else
            absr = -in;
    endfunction
//endpackage
`endif  // _UTIL_SV_