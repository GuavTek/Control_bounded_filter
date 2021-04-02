#include "tb.h"

#define N 3
#define SAMPLES_LENGTH 32767

sc_uint <1> samples[N][SAMPLES_LENGTH];

// Source thread
void tb::source()
{
    // Reset the output metaport and cycle the design's reset
    esc_printf("Running reset cycle\n");

    outputs.reset();
    rst = 0;
    wait(2);
    rst = 1;
    wait();

    esc_printf("Source started...\n");

    Batch_filter_INPUT_DT stimuli;

    // Load stimuli
    std::ifstream ins("hardware_signals.csv");
    if(ins.is_open()){
        int x = 0;
        int y = 0;
        while(!ins.eof()){
            if(y >= N){
                esc_log_message("tb", esc_warning, "Warning, stimuli file contains more channels");
            }
            char buf;
            ins >> buf;
            if (x < SAMPLES_LENGTH){
                if (buf == '1'){
                    samples[y][x] = 1;
                    x++;
                } else if (buf == '0'){
                    samples[y][x] = 0;
                    x++;
                }
            }
            if (buf == ']'){
                esc_printf("Loaded signal channel %d with length %d\n", y, x);
                y++;
                x = 0;
            }
        }
        ins.close();
    } else {
        // Throw error
        esc_log_message("tb", esc_fatal, "Failed to open stimuli file");
        esc_printf("No input file\n");
    }

    esc_printf("Applying stimuli\n");

    // Write a set of values to the dut
    for (int i = 0; i < SAMPLES_LENGTH; i++)
    {

        // Logging
        if(i % 256 == 0){
            esc_printf("Running input iteration %d\n", i);
        }

        // Write values to the DUT
        for (int n = 0; n < N; n++)
        {
            stimuli.Samples[n] = samples[n][i];
        }
        outputs.put(stimuli);
        wait();
    }

    esc_printf("Source finished\n");
    while(1){
        // Let sink finish
        outputs.put(stimuli);
        wait();
    }
}

// Read all the expected values from the design
void tb::sink()
{
    inputs.reset();
    wait();                     // to synchronize with reset
    
    esc_printf("Sink started...\n");

    std::ofstream ros("Results.csv");
    if(!ros.is_open()){
        esc_log_message("tb", esc_fatal, "Could not open output file");
        esc_printf("No output file\n");
    }

    Batch_filter_OUTPUT_DT val;
    val = inputs.get();
    wait();

    esc_printf("Discarding empty results\n");

    // Discard initial empty results.
    while(val.Result == 0.0){
        val = inputs.get();
        wait();
    }
    ros << val.Result;

    esc_log_message("tb", esc_note, "Sink receiving");

    esc_printf("Reading results\n");

    for (int i = 1; i < SAMPLES_LENGTH; i++)
    {
        // Read values from the DUT
        ros << ',';
        ros << ' ';
        val = inputs.get();
        ros << val.Result;
        wait();
    }
    ros.close();
    
    esc_printf("Sink done");

    esc_stop();
}

