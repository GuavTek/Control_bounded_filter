// Misc utilities used in several modules
`define EXP_W 5
`define MANT_W 11

typedef struct packed { 
    logic sign; 
    logic signed[EXP_W-1:0] exp;
    logic[MANT_W-1:0] mantis;
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

function real ftor(floatType in);
    begin
    logic[$bits(floatType.mantis):0] tempF;
    real tempR;

    tempF = {1'b1, in.mantis};
    
    if (in.sign) begin
        tempR = real'(-tempF);
    end else begin
        tempR = real'(tempF);
    end

    ftor = tempR * 2**in.exp;
    end
endfunction