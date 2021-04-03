
#ifndef __BATCH_FILTER__H
#define __BATCH_FILTER__H

#include "cynw_p2p.h"

#include "Batch_filter_input_type.h"
#include "Batch_filter_output_type.h"

// Filter config
#define N 3
#define BUFFER_SIZE 512

SC_MODULE(Batch_filter)
{
    public:
    cynw_p2p < Batch_filter_INPUT_DT  >::in     inputs;
    cynw_p2p < Batch_filter_OUTPUT_DT >::out    outputs;
    
    // Internal variables
    unsigned int stime;

    // Define recursion registers
    Complex lookaheadR[N];
    Complex backR[N];
    Complex forwardR[N];

    // Declaration of clock and reset parameters
    sc_in_clk               clk;
    sc_in < bool >          rst;
    SC_CTOR(Batch_filter):inputs("inputs"), outputs("outputs"), clk("clk"), rst("rst")
    {
        SC_CTHREAD(thread1, clk.pos());
        reset_signal_is(rst,0);
        
        // Connect the clk and rst signals to the metaports
        inputs.clk_rst(clk, rst);
        outputs.clk_rst(clk, rst);
    }
    void thread1();
    
    Batch_filter_OUTPUT_DT Calculate(Batch_filter_INPUT_DT);
    void Propagate_regs();
};

#endif

