
#ifndef __PARALLEL_FILTER__H
#define __PARALLEL_FILTER__H

#include "cynw_p2p.h"

#include "Parallel_filter_input_type.h"
#include "Parallel_filter_output_type.h"

SC_MODULE(Parallel_filter)
{
    public:
    cynw_p2p < Parallel_filter_INPUT_DT  >::in     inputs;
    cynw_p2p < Parallel_filter_OUTPUT_DT >::out    outputs;
    
    // Declaration of clock and reset parameters
    sc_in_clk               clk;
    sc_in < bool >          rst;
    SC_CTOR(Parallel_filter):inputs("inputs"), outputs("outputs"), clk("clk"), rst("rst")
    {
        SC_CTHREAD(thread1, clk.pos());
        reset_signal_is(rst,0);
        
        // Connect the clk and rst signals to the metaports
        inputs.clk_rst(clk, rst);
        outputs.clk_rst(clk, rst);
    }
    void thread1();
    
    Parallel_filter_OUTPUT_DT my_function(Parallel_filter_INPUT_DT);
};

#endif

