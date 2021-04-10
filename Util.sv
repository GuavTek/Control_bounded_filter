// Misc utilities used in several modules

typedef struct packed {
    logic sign;
    logic signed[4:0] exp;
    logic[9:0] mantis;
} floatType;

typedef struct packed {
    floatType r;
    floatType i;
} complex;

typedef enum int { 
    ADD = 0,
    MULT = 1
} FPU_opcode;

function floatType rtof(real in);
    begin
    floatType temp;
    int unsigned mant;
    int signed exponent = $clog2(in);
    temp.exp = exponent;
        
    if (in >= 0) begin
        temp.sign = 0;
        mant = (in * 2**($bits(temp.mantis)-exponent));
    end else begin
        temp.sign = 1;
        mant = (-in * 2**($bits(temp.mantis)-exponent));
    end

    temp.mantis = mant;
    rtof = temp;
    end
endfunction
