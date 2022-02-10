`include "HardFloat-1/source/HardFloat_consts.vi"
`include "HardFloat-1/source/HardFloat_specialize.vi"
`include "HardFloat-1/source/HardFloat_primitives.v"
`include "HardFloat-1/source/isSigNaNRecFN.v"
`include "HardFloat-1/source/HardFloat_rawFN.v"
`include "HardFloat-1/source/fNToRecFN.v"
`include "HardFloat-1/source/recFNToFN.v"
`include "HardFloat-1/source/addRecFN.v"
`include "HardFloat-1/source/mulRecFN.v"

`include "../sv/Data/Coefficients_Fixedpoint.sv"
`include "../sv/RAM.sv"
`include "../sv/Batch_Flp.sv"
`include "../sv/Util.sv"
`include "Util_TB.sv"
`include "TB_Common.sv"
`include "../sv/FPU.sv"
`include "FPU_prop.sv"
//`include "RAM_prop.sv"
//`include "LUT_prop.sv"
//`include "RecursionModule_prop.sv"
//`include "TopBatch_prop.sv"

`ifndef DEPTH
    `define DEPTH 220
`endif

`ifndef DSR
    `define DSR 1
`endif

`ifndef OUT_FILE
    `define OUT_FILE results_batch
`endif

`define TestLength 24000

module TB_Batch_Flp #() ();
    logic rst;
    logic clk;
    import Coefficients_Fx::*;

    localparam int DownSampleDepth = ($ceil((0.0 + `DEPTH) / `DSR));
    localparam SampleWidth = N*`DSR; 

    // Instantiate common testbench objects
    logic[N-1:0] inSample;
    logic[`OUT_WIDTH-1:0] dutResult;
    logic isValid;
    TB_COM #(.N(N), .TestLength(`TestLength), .DSR(`DSR), .OUT_FILE(`STRINGIFY(`OUT_FILE))) com1 (.sample(inSample), .clk(clk), .rst(rst), .result(dutResult), .valid(isValid));

    // Instantiate DUTs
    logic[SampleWidth-1:0] sampleDataOut1, sampleDataOut2, sampleDataOut3, sampleDataIn;
    logic[$clog2(4*DownSampleDepth)-1:0] sampleAddrIn, sampleAddrOut1, sampleAddrOut2, sampleAddrOut3;
    logic[`OUT_WIDTH-1:0] resDataInB, resDataInF, resDataOutB, resDataOutF;
    logic[$clog2(2*DownSampleDepth)-1:0] resAddrInB, resAddrInF, resAddrOutB, resAddrOutF;
    logic sampleClk, resClkF, resClkB, sampleWrite, resWriteB, resWriteF;
    RAM_triple #(.depth(4*DownSampleDepth), .d_width(SampleWidth)) sample (.clk(sampleClk), .rst(rst), .write(sampleWrite), .dataIn(sampleDataIn), .addrIn(sampleAddrIn), 
            .dataOut1(sampleDataOut1), .dataOut2(sampleDataOut2), .dataOut3(sampleDataOut3), .addrOut1(sampleAddrOut1), .addrOut2(sampleAddrOut2), .addrOut3(sampleAddrOut3));

    RAM_single #(.depth(2*DownSampleDepth), .d_width(`OUT_WIDTH)) calcB (.clk(resClkB), .rst(rst), .write(resWriteB), .dataIn(resDataInB), .addrIn(resAddrInB),
            .dataOut(resDataOutB), .addrOut(resAddrOutB));
    RAM_single #(.depth(2*DownSampleDepth), .d_width(`OUT_WIDTH)) calcF (.clk(resClkF), .rst(rst), .write(resWriteF), .dataIn(resDataInF), .addrIn(resAddrInF),
            .dataOut(resDataOutF), .addrOut(resAddrOutF));

    Batch_Flp #(.depth(`DEPTH), .DSR(`DSR), .n_exp(`EXP_W), .n_mant(`MANT_W)) DUT_Batch ( .rst(rst), .clk(clk), .in(inSample), .out(dutResult), .valid(isValid),
    .sampleAddrIn(sampleAddrIn), .sampleAddrOut1(sampleAddrOut1), .sampleAddrOut2(sampleAddrOut2), .sampleAddrOut3(sampleAddrOut3),
	.sampleClk(sampleClk), .sampleWrite(sampleWrite), .sampleDataIn(sampleDataIn),
	.sampleDataOut1(sampleDataOut1), .sampleDataOut2(sampleDataOut2), .sampleDataOut3(sampleDataOut3),
    .resAddrInF(resAddrInF), .resAddrInB(resAddrInB), .resAddrOutF(resAddrOutF), .resAddrOutB(resAddrOutB),
	.resClkF(resClkF), .resClkB(resClkB), .resWriteF(resWriteF), .resWriteB(resWriteB),
	.resDataInF(resDataInF), .resDataInB(resDataInB), .resDataOutF(resDataOutF), .resDataOutB(resDataOutB));
    

    // dummy type (so compiler knows there is a datatype with this name)
    typedef struct packed { 
        logic dum;
    } float_t;

    // Bind Modules to property checkers
    bind FPU FPU_prop #(.op(op), .n_exp(n_exp), .n_mant(n_mant), .float_t(float_t)) flprop_i (.*);  
    //bind RAM_single RAM_single_prop #(.depth(depth), .d_width(d_width)) ramsprop_i (.rst(rst), .*);
    //bind RAM_triple RAM_triple_prop #(.depth(depth), .d_width(d_width)) ramtprop_i (.*);
    //bind LUT LUT_prop #(.size(size), .fact(fact)) lutprop_i (.*);
    //bind RecursionModule RecursionModule_prop #(.factorR(factorR), .factorI(factorI)) Recprop_i (.*);
    //bind Batch_top Batch_top_prop #(.depth(depth), .DSR(DSR)) batchprop_i (.*);

endmodule