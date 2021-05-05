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
        HLS_FLATTEN_ARRAY(lookaheadR);
        HLS_FLATTEN_ARRAY(backR);
        HLS_FLATTEN_ARRAY(forwardR);

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
    static uint indexOut = 0;
    static sc_uint < 2 > cycle = 0;
    static sc_uint < 1 > cycleOut = 0;
    const uint width = 32;

    // Define buffers
    static Batch_filter_INPUT_DT::raw_type sample[4][BUFFER_SIZE];
    static sc_bv < N*width > calcF[2][BUFFER_SIZE];
    static sc_bv < N*width > calcB[2][BUFFER_SIZE];
    // Flatten arrays
    //HLS_FLATTEN_ARRAY(sample);
    // Split arrays
    HLS_SEPARATE_ARRAY(sample);
    HLS_MAP_TO_MEMORY(sample, "DualRAM");

    //HLS_SEPARATE_ARRAY(calcF);
    //HLS_SEPARATE_ARRAY(calcB);
    HLS_MAP_TO_MEMORY(calcF, "DualRAM");
    HLS_MAP_TO_MEMORY(calcB, "DualRAM");

    indexOut = index;

    if (indexOut == 0){
        cycleOut = !cycleOut;
    }

    index++;

    if (index == BUFFER_SIZE){
        index = 0;
        cycle++;

        stime <<= 1;
        stime[0] = 1;

    }

    uint reIndex = BUFFER_SIZE - index - 1;
    uint reIndexOut = BUFFER_SIZE - indexOut - 1;
    sc_uint < 2 > cycle0 = cycle;
    sc_uint < 2 > cycle1 = (cycle+1);
    sc_uint < 2 > cycle2 = (cycle+2);
    sc_uint < 2 > cycle3 = (cycle+3);

    // Load inputs
    cynw_interpret(var, sample[cycle3][index]);

    // Finish startup phase
    if(stime[2]){
        // Computation
        Batch_filter_INPUT_DT rf;
        static Batch_filter_INPUT_DT rff;
        Batch_filter_INPUT_DT rb;
        rf = rff;

        cynw_interpret(sample[cycle0][index], rff);
        cynw_interpret(sample[cycle0][reIndex], rb);

        for (uint n = 0; n < N; n++){
            HLS_UNROLL_LOOP(ALL, "Computation");

            // Backward recursion
            calcB[cycleOut][reIndexOut].range((n+1)*width-1,n*width) = (Wbr[n] * backR[n].real - Wbi[n] * backR[n].imag).raw_bits();

            Complex tempValBack;
            for(uint m = 0; m < N; m++){
                if(rb.Samples[m] == 1){
                    tempValBack.real += Fbr[n][m];
                    tempValBack.imag += Fbi[n][m];
                } else {
                    tempValBack.real -= Fbr[n][m];
                    tempValBack.imag -= Fbi[n][m];
                }
            }

            if(index == 0){
                tempValBack.real += Lbr[n] * lookaheadR[n].real - Lbi[n] * lookaheadR[n].imag;
                tempValBack.imag += Lbr[n] * lookaheadR[n].imag + Lbi[n] * lookaheadR[n].real;
            } else {
                tempValBack.real += Lbr[n] * backR[n].real - Lbi[n] * backR[n].imag;
                tempValBack.imag += Lbr[n] * backR[n].imag + Lbi[n] * backR[n].real;
            }

            backR[n].real = tempValBack.real;
            backR[n].imag = tempValBack.imag;

            // Forward recursion
            calcF[cycleOut][indexOut].range((n+1)*width-1,n*width) = (Wfr[n] * forwardR[n].real - Wfi[n] * forwardR[n].imag).raw_bits();

            Complex tempValForward;
            for(uint m = 0; m < N; m++){
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

        }
    }

    // Lookahead
    Batch_filter_INPUT_DT look;
    cynw_interpret(sample[cycle2][reIndex], look);
    for (uint n = 0; n < N; n++){
        HLS_UNROLL_LOOP(ALL, "Lookahead");
        Complex tempVal;
        for(uint m = 0; m < N; m++){
            if(look.Samples[m] == 1){
                tempVal.real += Fbr[n][m];
                tempVal.imag += Fbi[n][m];
            } else {
                tempVal.real -= Fbr[n][m];
                tempVal.imag -= Fbi[n][m];
            }
        }

        if(index != 0) {
            tempVal.real += Lbr[n] * lookaheadR[n].real - Lbi[n] * lookaheadR[n].imag;
            tempVal.imag += Lbi[n] * lookaheadR[n].real + Lbr[n] * lookaheadR[n].imag;
        }
        lookaheadR[n].real = tempVal.real;
        lookaheadR[n].imag = tempVal.imag;

    }

    // Load outputs
    floatType tempOut;
    for (uint n = 0; n < N; n++){
        HLS_UNROLL_LOOP(ALL, "Outputs");
        floatType tempF;
        floatType tempB;
        sc_bv < width > vecF;
        sc_bv < width > vecB;
        vecF = calcF[!cycleOut][indexOut].range((n+1)*width-1,n*width);
        vecB = calcB[!cycleOut][indexOut].range((n+1)*width-1,n*width);

        tempF.raw_bits(vecF);
        tempB.raw_bits(vecB);
        tempOut += tempF + tempB;
    }

    my_outputs.Result = tempOut;
    return (my_outputs);
}

