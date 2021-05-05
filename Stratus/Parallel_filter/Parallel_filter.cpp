#include "FloatType.h"
#include "Parallel_filter.h"
#include "Coefficients.h"
#include "cynw_utilities.h"
#include <math.h>
#define STAGES 120
#define N 3

const int STAGES_LOG2 = 8; //ceil(log2(STAGES));

typedef unsigned int uint;

sc_bv< N > buffer[STAGES+1];

sc_uint< STAGES_LOG2 > startTime;

// The thread function for the design
void Parallel_filter::thread1()
{
    // Reset the interfaces
    {
        CYN_PROTOCOL("reset");
        
        inputs.reset();
        outputs.reset();
        HLS_MAP_TO_REG_BANK(buffer);

        startTime = 0;
        
        wait();
    }
    
    // Main execution loop
    while (1)
    {
        Parallel_filter_INPUT_DT  input_val = inputs.get();
        
        Parallel_filter_OUTPUT_DT output_val = my_function(input_val);
        
        outputs.put(output_val);
    }
}
//
//  User's computation function
//
Parallel_filter_OUTPUT_DT Parallel_filter::my_function(Parallel_filter_INPUT_DT var)
{
    Parallel_filter_OUTPUT_DT my_outputs;

    // Shift buffer
    for(int i = STAGES; i > 0; i--){
        HLS_UNROLL_LOOP(ALL, "Input");
        buffer[i] = buffer[i-1];
    }

    // Load input buffer
    Parallel_filter_INPUT_DT::raw_type tempSam;
    cynw_interpret(var, tempSam);
    buffer[0] = tempSam;

    // Computation
    Complex temp[N];
    static Complex prev[N];
    for (uint i = 0; i < N; i++){
        HLS_UNROLL_LOOP(ALL, "Computation");
        for (uint j = 0; j < STAGES; j++){
            //HLS_PIPELINE_LOOP( HARD_STALL, 1, "Backward recursions");
            // Backward recursion
            sc_bv < N > bufSnip = buffer[j];

            for (uint k = 0; k < N; k++){
                if(bufSnip[k] == 1){
                    temp[i].real += Fbr[i][k] * Lbwr[i][j] - Fbi[i][k] * Lbwi[i][j];
                } else {
                    temp[i].real -= Fbr[i][k] * Lbwr[i][j] - Fbi[i][k] * Lbwi[i][j];
                }
            }
        }

        // Forward recursion
        if(startTime == STAGES){
        Complex tempIn = {0, 0};
        sc_bv < N > bufSnip = buffer[STAGES];
        for (uint k = 0; k < N; k++){
            if(bufSnip[k] == 1){
                tempIn.real += Ffr[i][k];
                tempIn.imag += Ffi[i][k];
            } else {
                tempIn.real -= Ffr[i][k];
                tempIn.imag -= Ffi[i][k];
            }
        }
        tempIn.real += prev[i].real * Lfr[i] - prev[i].imag * Lfi[i];
        tempIn.imag += prev[i].real * Lfi[i] + prev[i].imag * Lfr[i];
        prev[i].real = tempIn.real;
        prev[i].imag = tempIn.imag;
        } else {
            startTime++;
        }
    }

    floatType sum = 0;
    for(uint i = 0; i < N; i++){
        HLS_UNROLL_LOOP(ALL, "Results");
        sum += temp[i].real + prev[i].real * Wfr[i] - prev[i].imag * Wfi[i];
    }

    my_outputs.Result = sum;
    
    return (my_outputs);
}


