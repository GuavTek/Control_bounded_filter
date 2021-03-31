// Misc utilities used in several modules

typedef struct packed {
    logic sign;
    logic[4:0] signed exp;
    logic[9:0] mantis;
} float16;

typedef struct packed {
    float16 r;
    float16 i;
} complex;

typedef enum logic { 
    ADD,
    MULT
 } FPU_opcode;

function float16 rtof(real in);
    int signed exponent = $clog2(in);
    rtof.exp = exponent;
    
    if (in >= 0)
        rtof.sign = 0;
    else
        rtof.sign = 1;

    logic[$bits(float16.mantis):0] temp;
    temp = in * 2**(-exponent);
    rtof.mantis = temp[$bits(float16.mantis-1:0)];

endfunction
