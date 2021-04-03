//#include "FloatType.h"
#include "Batch_filter.h"
#include "Coefficients.h"

typedef unsigned int uint;

// The thread function for the design
void Batch_filter::thread1()
{
    // Reset the interfaces
    {
        CYN_PROTOCOL("reset");
        
        inputs.reset();
        outputs.reset();
        
        // Flatten recursion registers


        stime = 0;

        wait();
    }
    
    // Main execution loop
    while (1)
    {
        Batch_filter_INPUT_DT  input_val = inputs.get();

        Batch_filter_OUTPUT_DT output_val = Calculate(input_val);

        outputs.put(output_val);
    }
}

//
//  User's computation function
//
Batch_filter_OUTPUT_DT Batch_filter::Calculate(Batch_filter_INPUT_DT var)
{
    Batch_filter_OUTPUT_DT my_outputs;
    static uint index = 0;
    static uint cycle = 0;

    // Define buffers
    static Batch_filter_INPUT_DT::raw_type sample[4][BUFFER_SIZE];
    static float16 calcF[2][N][BUFFER_SIZE];
    static float16 calcB[2][N][BUFFER_SIZE];
    static float16 delayF[N];
    // Flatten delayF

    index++;

    if (index == BUFFER_SIZE){
        index = 0;
        cycle++;

        if (stime < 3){
            stime++;
        }/**/
    }

    uint reIndex = BUFFER_SIZE - index - 1;
    uint cycle0 = cycle % 4;
    uint cycle1 = (cycle+1) % 4;
//    uint cycle2 = (cycle+2) % 4;
    uint cycle3 = (cycle+3) % 4;

    // Load inputs
    cynw_interpret(var, sample[cycle0][index]);

    // Lookahead
    Batch_filter_INPUT_DT look;
    cynw_interpret(sample[cycle1][reIndex], look);
    for (int n = 0; n < N; n++){
        HLS_UNROLL_LOOP(ALL, "Lookahead");
        Complex tempVal;
        for(int m = 0; m < N; m++){
            if(look.Samples[m] == 1){
                tempVal.real += Fbr[n][m];
                tempVal.imag += Fbi[n][m];
            } else {
                tempVal.real -= Fbr[n][m];
                tempVal.imag -= Fbi[n][m];
            }
        }
        if (index == 0){
            // New batch, reset register
            lookaheadR[n].real = tempVal.real;
            lookaheadR[n].imag = tempVal.imag;
        } else {
            lookaheadR[n].real = Lbr[n] * lookaheadR[n].real - Lbi[n] * lookaheadR[n].imag + tempVal.real;
            lookaheadR[n].imag = Lbi[n] * lookaheadR[n].real + Lbr[n] * lookaheadR[n].imag + tempVal.imag;
        }
    }


    // Finish startup phase
    if(stime >= 3){
        // Computation
        Batch_filter_INPUT_DT rf;
        Batch_filter_INPUT_DT rb;
        cynw_interpret(sample[cycle3][index], rf);
        cynw_interpret(sample[cycle3][reIndex], rb);
        for (int n = 0; n < N; n++){
            HLS_UNROLL_LOOP(ALL, "Computation");
            // Backward recursion
            Complex tempValBack;
            for(int m = 0; m < N; m++){
                if(rb.Samples[m] == 1){
                    tempValBack.real += Fbr[n][m];
                    tempValBack.imag += Fbi[n][m];
                } else {
                    tempValBack.real -= Fbr[n][m];
                    tempValBack.imag -= Fbi[n][m];
                }
            }

            if (index == 0){
                tempValBack.real += Lbr[n] * lookaheadR[n].real - Lbi[n] * lookaheadR[n].imag;
                tempValBack.imag += Lbr[n] * lookaheadR[n].imag + Lbi[n] * lookaheadR[n].real;
            } else {
                tempValBack.real += Lbr[n] * backR[n].real - Lbi[n] * backR[n].imag;
                tempValBack.imag += Lbr[n] * backR[n].imag + Lbi[n] * backR[n].real;
            }

            backR[n].real = tempValBack.real;
            backR[n].imag = tempValBack.imag;

            calcB[cycle0 % 2][n][reIndex] = Wbr[n] * tempValBack.real - Wbi[n] * tempValBack.imag;

            // Forward recursion
            Complex tempValForward;
            for(int m = 0; m < N; m++){
                if(rf.Samples[m] == 1){
                    tempValForward.real += Ffr[n][m];
                    tempValForward.imag += Ffi[n][m];
                } else {
                    tempValForward.real -= Ffr[n][m];
                    tempValForward.imag -= Ffi[n][m];
                }
            }

            tempValForward.real += Lfr[n] * forwardR[n].real - Lfi[n] * forwardR[n].imag;
            tempValForward.imag += Lfr[n] * forwardR[n].imag + Lfi[n] * forwardR[n].real;

            forwardR[n].real = tempValForward.real;
            forwardR[n].imag = tempValForward.imag;

            calcF[cycle0 % 2][n][index] = delayF[n];
            delayF[n] = Wfr[n] * tempValForward.real - Wfi[n] * tempValForward.imag;

        }
    }

    // Load outputs
    float16 tempOut;
    for (int n = 0; n < N; n++){
        HLS_UNROLL_LOOP(ALL, "Outputs");
        tempOut += calcF[cycle1 % 2][n][index] + calcB[cycle1 % 2][n][index];
    }

    my_outputs.Result = tempOut;
    return (my_outputs);
}
/*
void Batch_filter::Propagate_regs(){
    // Propagate registers
    for(int i = 0; i < N; i++){
//        HLS_UNROLL_LOOP( ALL, "Register Propagation");
        for(int j = 0; j < BUFFER_SIZE; i++){
            calcOutF[i][j] = calcInF[i][j];
            calcOutB[i][j] = calcInB[i][j];
            sampleCalc[i][j] = sampleHold[i][j];
            sampleHold[i][j] = sampleLook[i][j];
            sampleLook[i][j] = sampleIn[i][j];
        }
        backR[i] = lookaheadR[i];
        lookaheadR[i].real = 0.0;
        lookaheadR[i].imag = 0.0;
    }

    if (stime < 3){
        stime++;
    }
//    return;
}
*/
