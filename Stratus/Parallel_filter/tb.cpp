

#include "tb.h"


// Source thread
void tb::source()
{
    // Reset the output metaport and cycle the design's reset
    outputs.reset();
    rst = 0;
    wait(2);
    rst = 1;
    wait();
    
    // Write a set of values to the dut
    for (int i = 0; i < 10; i++)
    {
        // Write values to the DUT
    }
}

// Read all the expected values from the design
void tb::sink()
{
    inputs.reset();
    wait();                     // to synchronize with reset
    
    
    for (int i = 0; i < 10; i++)
    {
        // Read values from the DUT
    }
    
    printf("NOTE: You need to add code to the tb.cpp file in order to get a working simulation.\n");
    
    esc_stop();
}

