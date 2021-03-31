#ifndef __TB__H
#define __TB__H

#include "cynw_p2p.h"

#include "Batch_filter_input_type.h"
#include "Batch_filter_output_type.h"

SC_MODULE(tb)
{
    public:
    cynw_p2p < Batch_filter_OUTPUT_DT >::base_in    inputs;
    cynw_p2p < Batch_filter_INPUT_DT >::base_out    outputs;
    
    // Declaration of clock and reset parameters
    sc_in_clk                   clk;
    sc_out < bool >             rst;
    sc_in < bool >              rst_in; // sampling version of "rst"
    
    SC_CTOR(tb)
    {
        SC_CTHREAD(source, clk.pos());
        SC_CTHREAD(sink, clk.pos());
        reset_signal_is(rst_in,0);
        rst_in(rst);
    }
    void source();
    void sink();
};

#endif

