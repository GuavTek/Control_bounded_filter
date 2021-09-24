#ifndef BUFFER_TYPES_H
#define BUFFER_TYPES_H

#include "FloatType.h"

typedef Complex ComplexBuff_t[BUFFER_SIZE];
typedef sc_uint <1> SampleBuff_t[N][BUFFER_SIZE];

inline void cpComplexBuff(ComplexBuff_t &to, ComplexBuff_t &from){
    for(int i = 0; i < BUFFER_SIZE; i++){
        to[i].real = from[i].real;
        to[i].imag = from[i].imag;
    }
}

inline void cpSampleBuff(SampleBuff_t &to, SampleBuff_t &from){
    for(int i = 0; i < BUFFER_SIZE; i++){
        to[i] = from[i];
    }
}

#endif // BUFFER_TYPES_H
