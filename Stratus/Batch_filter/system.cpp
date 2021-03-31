#include "system.h"

void TOP::initInstances()
{
    m_dut = new Batch_filter_wrapper("Batch_filter_wrapper");
    
    // Connect the design module
    m_dut->clk(clk);
    m_dut->rst(rst);
    m_dut->inputs(inputs_chan);
    m_dut->outputs(outputs_chan);
    
    
    // Connect the testbench
    m_tb = new tb("tb");
    m_tb->clk(clk);
    m_tb->rst(rst);
    m_tb->outputs(inputs_chan);
    m_tb->inputs(outputs_chan);
}

void TOP::deleteInstances()
{
    delete m_tb;
    delete m_dut;
}

