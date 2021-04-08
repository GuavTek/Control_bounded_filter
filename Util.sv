// Misc utilities used in several modules

typedef struct packed {
    logic sign;
    logic[4:0] signed exp;
    logic[9:0] mantis;
} floatType;

typedef struct packed {
    floatType r;
    floatType i;
} complex;

typedef enum logic { 
    ADD,
    MULT
 } FPU_opcode;

function floatType rtof(real in);
    int signed exponent = $clog2(in);
    rtof.exp = exponent;
    
    logic[$bits(floatType.mantis):0] temp;
    if (in >= 0) begin
        rtof.sign = 0;
        temp = int'(in * 2**(-exponent));
    end else begin
        rtof.sign = 1;
        temp = int'(-in * 2**(-exponent));
    end

    rtof.mantis = temp[$bits(floatType.mantis)-1:0];

endfunction
