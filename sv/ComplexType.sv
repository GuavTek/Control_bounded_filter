`ifndef COMPLEXTYPE_SV_
`define COMPLEXTYPE_SV_

typedef struct {
    shortreal r = 0.0;
    shortreal i = 0.0;
} complex;

// Arithmetic functions
function complex caddcc (input  complex a, b);
    begin
        caddcc.r = a.r + b.r;
        caddcc.i = a.i + b.i;
    end
endfunction

function complex caddrc (input  shortreal a, 
                                complex b);
    begin
        caddrc.r = a + b.r;
        caddrc.i = b.i;
    end
endfunction

function complex caddcr (input  complex a, 
                                shortreal b);
    begin
        caddcr.r = a.r + b;
        caddcr.i = a.i;
    end
endfunction

function complex caddrr (input shortreal a, b);
    begin
        caddrr.r = a + b;
        caddrr.i = 0;
    end
endfunction

function shortreal raddcc (input    complex a, b);
    begin
        raddcc = a.r + b.r;
    end
endfunction

function shortreal raddrc (input    shortreal a,
                                    complex b);
    begin
        raddrc = a + b.r;
    end
endfunction

function shortreal raddcr (input    complex a, 
                                    shortreal b);
    begin
        raddcr = a.r + b;
    end
endfunction

function complex csubcc (input  complex a, b);
    begin
        csubcc.r = a.r - b.r;
        csubcc.i = a.i - b.i;
    end
endfunction

function complex csubrc (input  shortreal a, 
                                complex b);
    begin
        csubrc.r = a - b.r;
        csubrc.i = 0 - b.i;
    end
endfunction

function complex csubcr (input  complex a, 
                                shortreal b);
    begin
        csubcr.r = a.r - b;
        csubcr.i = a.i;
    end
endfunction

function complex csubrr (input shortreal a, b);
    begin
        csubrr.r = a - b;
        csubrr.i = 0;
    end
endfunction

function shortreal rsubcc (input    complex a, b);
    begin
        rsubcc = a.r - b.r;
    end
endfunction

function shortreal rsubrc (input    shortreal a,
                                    complex b);
    begin
        rsubrc = a + b.r;
    end
endfunction

function shortreal rsubcr (input    complex a, 
                                    shortreal b);
    begin
        rsubcr = a.r + b;
    end
endfunction

function complex cmulcc (input  complex a, b);
    begin
        cmulcc.r = (a.r * b.r) - (a.i * b.i);
        cmulcc.i = (a.i * b.r) + (a.r * b.i);
    end
endfunction

function shortreal rmulcc (input    complex a, b);
    begin
        rmulcc = (a.r * b.r) - (a.i * b.i);
    end
endfunction

function complex rtoc (input  shortreal a);
    begin
        rtoc.r = a;
        rtoc.i = 0;
    end
endfunction

function complex ltoc (input   logic[63:0] a);
    ltoc.r = $bitstoshortreal(a[63:32]); //Not supported?!
    ltoc.i = $bitstoshortreal(a[31:0]);
endfunction

function logic[63:0] ctol (input complex a);
    ctol[63:32] = $shortrealtobits(a.r); //Not supported?!
    ctol[31:0] = $shortrealtobits(a.i);
endfunction

/*// Overload declarations
bind + function complex caddcc(complex, complex);
bind + function complex caddrc(shortreal, complex);
bind + function complex caddcr(complex, shortreal);
bind + function complex caddrr(shortreal, shortreal);
bind + function shortreal raddcc(complex, complex);
bind + function shortreal raddrc(shortreal, complex);
bind + function shortreal raddcr(complex, shortreal);
bind - function complex csubcc(complex, complex);
bind - function complex csubrc(shortreal, complex);
bind - function complex csubcr(complex, shortreal);
bind - function complex csubrr(shortreal, shortreal);
bind - function shortreal rsubcc(complex, complex);
bind - function shortreal rsubrc(shortreal, complex);
bind - function shortreal rsubcr(complex, shortreal);
bind * function complex cmulcc(complex, complex);
bind = function complex rtoc (shortreal);
*/

`endif