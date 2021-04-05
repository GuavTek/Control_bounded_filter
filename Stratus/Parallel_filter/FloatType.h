#ifndef FLOATTYPE_H
#define FLOATTYPE_H

#include <cynw_cm_float.h>

typedef cynw_cm_float<5,14,CYNW_BEST_ACCURACY,CYNW_NEAREST,0> floatType;

typedef struct {
    floatType real;
    floatType imag;
} Complex;


#endif // FLOATTYPE_H
