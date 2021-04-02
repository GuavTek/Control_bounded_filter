#ifndef FLOATTYPE_H
#define FLOATTYPE_H

#include <cynw_cm_float.h>

typedef cynw_cm_float<5,14,CYNW_REDUCED_ACCURACY,CYNW_NEAREST,0> float16;

typedef struct {
    float16 real;
    float16 imag;
} Complex;


#endif // FLOATTYPE_H
