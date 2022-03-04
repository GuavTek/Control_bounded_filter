`include "../sv/Batch_Fxp.sv"
`include "../sv/Util.sv"
`include "Util_TB.sv"
`include "TB_Common.sv"
`include "../sv/FxpPU.sv"
`include "../sv/RAM.sv"
`include "FxpPU_prop.sv"
//`include "FixLUT_prop.sv"
`include "Batch_Fxp_prop.sv"

`define TestLength 24000

`ifndef DEPTH
    `define DEPTH 220
`endif

`ifndef DSR1
    `define DSR1 2
`endif

`ifndef DSR2
    `define DSR2 6
`endif

`ifndef DSR
    `define DSR (`DSR1 * `DSR2)
`endif

`ifndef OUT_FILE
    `define OUT_FILE results_batch_fix
`endif

module TB_Batch_Fxp #() ();
    logic rst;
    logic clk;
    import Coefficients_Fx::*;
    
    localparam int DownResultDepth = $ceil((0.0 + `DEPTH) / `DSR);
    localparam int DownSampleDepth = DownResultDepth; // DownResultDepth * `DSR2;
    localparam SampleWidth = N*`DSR; 

    // Instantiate common testbench objects
    logic[N-1:0] inSample;
    logic[`OUT_WIDTH-1:0] dutResult;
    logic isValid;
    TB_COM #(.N(N), .TestLength(`TestLength), .DSR(`DSR), .OUT_FILE(`STRINGIFY(`OUT_FILE))) com1 (.sample(inSample), .clk(clk), .rst(rst), .result(dutResult), .valid(isValid));
    

    localparam out_w = `OUT_WIDTH;

    // Instantiate DUTs
    logic[SampleWidth-1:0] sampleDataOut1, sampleDataOut2, sampleDataOut3, sampleDataIn;
    logic[$clog2(4*DownSampleDepth)-1:0] sampleAddrIn, sampleAddrOut1, sampleAddrOut2, sampleAddrOut3;
    logic[out_w-1:0] resDataInB, resDataInF, resDataOutB, resDataOutF;
    logic[$clog2(2*DownResultDepth)-1:0] resAddrInB, resAddrInF, resAddrOutB, resAddrOutF;
    logic sampleClk, resClkF, resClkB, sampleWrite, resWriteB, resWriteF;
    RAM_triple #(.depth(4*DownSampleDepth), .d_width(SampleWidth)) sample (.clk(sampleClk), .rst(rst), .write(sampleWrite), .dataIn(sampleDataIn), .addrIn(sampleAddrIn), 
            .dataOut1(sampleDataOut1), .dataOut2(sampleDataOut2), .dataOut3(sampleDataOut3), .addrOut1(sampleAddrOut1), .addrOut2(sampleAddrOut2), .addrOut3(sampleAddrOut3));

    RAM_single #(.depth(2*DownResultDepth), .d_width(out_w)) calcB (.clk(resClkB), .rst(rst), .write(resWriteB), .dataIn(resDataInB), .addrIn(resAddrInB),
            .dataOut(resDataOutB), .addrOut(resAddrOutB));
    RAM_single #(.depth(2*DownResultDepth), .d_width(out_w)) calcF (.clk(resClkF), .rst(rst), .write(resWriteF), .dataIn(resDataInF), .addrIn(resAddrInF),
            .dataOut(resDataOutF), .addrOut(resAddrOutF));

    Batch_Fxp #(.depth(`DEPTH), .DSR(`DSR), .n_mant(`MANT_W), .n_int(`EXP_W)) DUT_Batch ( .rst(rst), .clk(clk), .in(inSample), .out(dutResult), .valid(isValid),
    .sampleAddrIn(sampleAddrIn), .sampleAddrOut1(sampleAddrOut1), .sampleAddrOut2(sampleAddrOut2), .sampleAddrOut3(sampleAddrOut3),
	.sampleClk(sampleClk), .sampleWrite(sampleWrite), .sampleDataIn(sampleDataIn),
	.sampleDataOut1(sampleDataOut1), .sampleDataOut2(sampleDataOut2), .sampleDataOut3(sampleDataOut3),
    .resAddrInF(resAddrInF), .resAddrInB(resAddrInB), .resAddrOutF(resAddrOutF), .resAddrOutB(resAddrOutB),
	.resClkF(resClkF), .resClkB(resClkB), .resWriteF(resWriteF), .resWriteB(resWriteB),
	.resDataInF(resDataInF), .resDataInB(resDataInB), .resDataOutF(resDataOutF), .resDataOutB(resDataOutB));
    
    
    // Bind Modules to property checkers
    bind FxpPU FxpPU_prop #(.op(op), .n_int(n_int), .n_mant(n_mant)) flprop_i (.*);
    //bind FixLUT FixLUT_prop #(.size(size), .fact(fact)) lutprop_i (.*);
    //bind Batch_Fixed_top Batch_Fixed_prop #(.depth(`DEPTH), .DSR(`DSR), .n_int(n_int), .n_mant(n_mant)) batchprop_i (.*);

endmodule