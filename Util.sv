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
    ADD,
    MULT
 } FPU_opcode;

function floatType rtof(real in);
    floatType temp;
    int signed exponent = $clog2(in);
    temp.exp = exponent;
    
    logic[$bits(temp.mantis):0] mant;
    if (in >= 0) begin
        temp.sign = 0;
        mant = int'(in * 2**(-exponent));
    end else begin
        temp.sign = 1;
        mant = int'(-in * 2**(-exponent));
    end

    temp.mantis = mant[$bits(temp.mantis)-1:0];
    rtof = temp;
endfunction
