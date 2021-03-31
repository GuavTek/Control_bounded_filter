#ifndef SYSTEM_H_INCLUDED
#define SYSTEM_H_INCLUDED

#include <systemc.h>
#include <esc.h>
#include "cynw_p2p.h"

#include "tb.h"
#include "Parallel_filter_input_type.h"
#include "Parallel_filter_output_type.h"
#include "Parallel_filter_wrap.h"

SC_MODULE(TOP)
{
    public:
    // cynw_p2p channels
    cynw_p2p < Parallel_filter_INPUT_DT >      inputs_chan;
    cynw_p2p < Parallel_filter_OUTPUT_DT >     outputs_chan;
    
    // clock and reset signals
    sc_clock            clk;
    sc_signal < bool >  rst;
    // The testbench and DUT modules.
    Parallel_filter_wrapper *m_dut;
    tb   *m_tb;
    
    void initInstances();
    void deleteInstances();
    
    SC_CTOR(TOP): clk("clk", CLOCK_PERIOD, SC_NS, 0.5, 0, SC_NS, true),
        inputs_chan("inputs_chan"),
        outputs_chan("outputs_chan"),
        rst("rst")
    {
        initInstances();
    }
    
    ~TOP()
    {
        deleteInstances();
    }
};

#endif // SYSTEM_H_INCLUDED

