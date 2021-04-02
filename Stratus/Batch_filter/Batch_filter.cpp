#include "FloatType.h"
#include "Coefficients.h"
#include "Batch_filter.h"

typedef unsigned int uint;

// The thread function for the design
void Batch_filter::thread1()
{
    // Reset the interfaces
    {
        CYN_PROTOCOL("reset");
        
        inputs.reset();
        outputs.reset();
        
        // Reset recursion registers
        for(int n = 0; n < N; n++){
            //lookaheadR[n].real = 0.0;
            //backR[n].real = 0.0;
            //forwardR[n].real = 0.0;
            //lookaheadR[n].imag = 0.0;
            //backR[n].imag = 0.0;
            //forwardR[n].imag = 0.0;
        }
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
    static sc_uint <1> sample[4][N][BUFFER_SIZE];
    static float16 calcF[2][N][BUFFER_SIZE];
    static float16 calcB[2][N][BUFFER_SIZE];
    static float16 delayF[N];

    index++;
    int reIndex = BUFFER_SIZE - index - 1;

    if (index == BUFFER_SIZE){
        index = 0;
        cycle++;
        //Propagate_regs();

        for (uint n = 0; n < N; n++)
        {
            backR[n].real = lookaheadR[n].real;
            backR[n].imag = lookaheadR[n].imag;
            lookaheadR[n].real = 0.0;
            lookaheadR[n].imag = 0.0; 
        }

        if (stime < 3){
            stime++;
        }/**/
    }

    uint cycle0 = cycle % 4;
    uint cycle1 = (cycle+1) % 4;
    uint cycle2 = (cycle+2) % 4;
    uint cycle3 = (cycle+3) % 4;

    // Load inputs
    for (int n = 0; n < N; n++){
        HLS_UNROLL_LOOP(ALL, "Input loading");
        // Load new samples
        sample[cycle0][n][index] = var.Samples[n];
    }

    // Lookahead
    for (int n = 0; n < N; n++){
        HLS_UNROLL_LOOP(ALL, "Lookahead");
        Complex tempVal;
        for(int m = 0; m < N; m++){
            if(sample[cycle1][m][reIndex] == 1){
                tempVal.real += Fbr[n][m];
                tempVal.imag += Fbi[n][m];
            } else {
                tempVal.real -= Fbr[n][m];
                tempVal.imag -= Fbi[n][m];
            }
        }
        lookaheadR[n].real = Lbr[n] * lookaheadR[n].real - Lbi[n] * lookaheadR[n].imag + tempVal.real;
        lookaheadR[n].imag = Lbi[n] * lookaheadR[n].real + Lbr[n] * lookaheadR[n].imag + tempVal.imag;
    }

    // Computation
    for (int n = 0; n < N; n++){
        HLS_UNROLL_LOOP(ALL, "Computation");
        // Backward recursion
        Complex tempValBack;
        for(int m = 0; m < N; m++){
            if(sample[cycle3][m][reIndex] == 1){
                tempValBack.real += Fbr[n][m];
                tempValBack.imag += Fbi[n][m];
            } else {
                tempValBack.real -= Fbr[n][m];
                tempValBack.imag -= Fbi[n][m];
            }
        }

        if(stime < 3){
            // Startup phase
            backR[n].real = 0;
            backR[n].imag = 0;
        } else {
            backR[n].real = Lbr[n] * backR[n].real - Lbi[n] * backR[n].imag + tempValBack.real;
            backR[n].imag = Lbr[n] * backR[n].imag + Lbi[n] * backR[n].real + tempValBack.imag;
        }

        calcB[cycle0 % 2][n][reIndex] = Wbr[n] * backR[n].real - Wbi[n] * backR[n].imag;

        // Forward recursion
        Complex tempValForward;
        for(int m = 0; m < N; m++){
            if(sample[cycle3][m][index] == 1){
                tempValForward.real += Ffr[n][m];
                tempValForward.imag += Ffi[n][m];
            } else {
                tempValForward.real -= Ffr[n][m];
                tempValForward.imag -= Ffi[n][m];
            }
        }

        if(stime < 3){
            // Startup phase
            forwardR[n].real = 0;
            forwardR[n].imag = 0;
        } else {
            forwardR[n].real = Lfr[n] * forwardR[n].real - Lfi[n] * forwardR[n].imag + tempValForward.real;
            forwardR[n].imag = Lfr[n] * forwardR[n].imag + Lfi[n] * forwardR[n].real + tempValForward.imag;
        }

        calcF[cycle0 % 2][n][index] = delayF[n];
        delayF[n] = Wfr[n] * forwardR[n].real - Wfi[n] * forwardR[n].imag;

    }

    // Load outputs
    float16 tempOut;
    for (int n = 0; n < N; n++){
        HLS_UNROLL_LOOP(ALL, "Outputs");
        tempOut += calcF[cycle1 % 2][n][index] + calcB[cycle1 % 2][n][index];
    }

    my_outputs.Result = (sc_int<20>) (tempOut * pow(2,14));
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
