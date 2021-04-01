

#include "tb.h"

#define N 3
#define SAMPLES_LENGTH 32767

sc_uint <1> samples[N][SAMPLES_LENGTH]

// Source thread
void tb::source()
{
    // Reset the output metaport and cycle the design's reset
    outputs.reset();
    rst = 0;
    wait(2);
    rst = 1;
//    wait();
    
    // Load stimuli
    std::ifstream ins("hardware_signals.csv");
    if(ins.is_open()){
        int x = 0;
        int y = 0;
        while(!ins.eof()){
            if(x >= SAMPLES_LENGTH){
                x = 0;
                y++;
            }
            if(y >= N){
                printf("Warning, stimuli outside buffer range");
                // error?
            }
            int buf = 99;
            ins >> buf;
            if (buf == 1){
                samples[y][x] = 1;
                x++;
            } else if (buf == 0){
                samples[y][x] = 0;
                x++;
            }
        }
        ins.close();
    } else {
        printf("Failed to open stimuli file");
        // Throw error
    }

    // Write a set of values to the dut
    for (int i = 0; i < SAMPLES_LENGTH; i++)
    {
        // Write values to the DUT
        Batch_filter_INPUT_DT stimuli[N]
        for (int n = 0; n < N; n++)
        {
            stimuli.Samples[n] = samples[n][i];
        }
        outputs.put(stimuli);
    }

    wait();
}

// Read all the expected values from the design
void tb::sink()
{
    inputs.reset();
    wait();                     // to synchronize with reset
    
    // Discard initial empty results.
    while(inputs.Result == 0.0);

    std::ofstream ros("Results.csv");
    if(!ros.is_open()){
        printf("Error! Could not open output file");
    }
    for (int i = 0; i < SAMPLES_LENGTH; i++)
    {
        if(i > 0){
            ros << " ,";
        }
        // Read values from the DUT
        Batch_filter_OUTPUT_DT val = inputs.get();
        ros << val.Result;
    }
    ros.close();
    
    
    esc_stop();
}

