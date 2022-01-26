`include "../sv/TopCumulFix.sv"
`include "../sv/Util.sv"
`include "Util_TB.sv"
`include "TB_Common.sv"
//`include "../sv/FixPU.sv"
`include "FixPU_prop.sv"
//`include "FixLUT_prop.sv"
//`include "TopBatchFix_prop.sv"

`include "../sv/Data/Coefficients_Fixedpoint.sv"
`define TestLength 24000

`ifndef DEPTH
    `define DEPTH 220
`endif

`ifndef OSR
    `define OSR 1
`endif

`ifndef OUT_FILE
    `define OUT_FILE results_cumul_fix
`endif

module TB_CUMUL_Fixed #() ();
    logic rst;
    logic clk;
    import Coefficients_Fx::*;

    localparam DownSampleDepth = $rtoi($ceil(`DEPTH / `OSR));
    localparam SampleWidth = N*`OSR; 

    // Instantiate common testbench objects
    logic[N-1:0] inSample;
    logic[`OUT_WIDTH-1:0] dutResult;
    logic isValid;
    TB_COM #(.N(N), .TestLength(`TestLength), .OSR(`OSR), .OUT_FILE(`STRINGIFY(`OUT_FILE))) com1 (.sample(inSample), .clk(clk), .rst(rst), .result(dutResult), .valid(isValid));

    localparam out_w = 14;

    // Instantiate DUTs
    Cumulative_Fixed_top #(.depth(`DEPTH), .OSR(`OSR), .n_mant(`MANT_W), .n_int(`EXP_W)) DUT_Cumul ( .rst(rst), .clk(clk), .in(inSample), .out(dutResult), .valid(isValid));
    
    
    // Bind Modules to property checkers
    bind FixPU FixPU_prop #(.op(op), .n_int(n_int), .n_mant(n_mant)) flprop_i (.*);
    //bind FixLUT FixLUT_prop #(.size(size), .fact(fact)) lutprop_i (.*);
    //bind Batch_Fixed_top Batch_Fixed_prop #(.depth(`DEPTH), .OSR(`OSR), .n_int(n_int), .n_mant(n_mant)) batchprop_i (.*);

endmodule