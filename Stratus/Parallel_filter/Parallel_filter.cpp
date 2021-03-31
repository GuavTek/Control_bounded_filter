#include "FloatType.h"
#include "Parallel_filter.h"
#include "Coefficients.h"
#include <math.h>
#define STAGES 128
#define N 3

sc_int<1> buffer[STAGES+1][N];

// The thread function for the design
void Parallel_filter::thread1()
{
    // Reset the interfaces
    {
        CYN_PROTOCOL("reset");
        
        inputs.reset();
        outputs.reset();
        
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

    for(int j = 0; j < N; j++){
        // Shift input buffer
        HLS_UNROLL_LOOP(ALL, "Sample shift-register");
        for(int i = 0; i < STAGES; i++){
            buffer[STAGES-i][j] = buffer[STAGES-i-1][j];
        }
        // Load input buffer
        buffer[0][j] = var.Samples[j];
    }

    // Computation
    Complex temp[N];
    static Complex prev[N];
    for (int i = 0; i < N; i++){
        HLS_UNROLL_LOOP(ALL, "Computation");
        for (int j = 0; j < STAGES; j++){
            HLS_PIPELINE_LOOP( HARD_STALL, 1, "Backward recursions");
            // Backward recursion
            for (int k = 0; k < N; k++){
                if(buffer[j][k] == 1){
                    temp[i].real += Fbr[i][k] * Lbwr[i][j] - Fbi[i][k] * Lbwi[i][j];
                } else {
                    temp[i].real -= Fbr[i][k] * Lbwr[i][j] - Fbi[i][k] * Lbwi[i][j];
                }
            }
        }

        // Forward recursion
        Complex tempIn = {0, 0};
        for (int k = 0; k < N; k++){
            if(buffer[STAGES][k] == 1){
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
    }

    float16 sum = 0;
    for(int i = 0; i < N; i++){
        HLS_UNROLL_LOOP(ALL, "Results");
        sum += temp[i].real + prev[i].real * Wfr[i] - prev[i].imag * Wfi[i];
    }

    my_outputs.Result = (sc_int<16>) (sum * pow(2,15));
    
    return (my_outputs);
}


