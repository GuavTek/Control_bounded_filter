`include "../sv/Cumulative_Fxp.sv"
`include "../sv/Util.sv"
`include "Util_TB.sv"
`include "TB_Common.sv"
//`include "../sv/FixPU.sv"
`include "FxpPU_prop.sv"
//`include "FixLUT_prop.sv"
//`include "TopBatchFix_prop.sv"

`define TestLength 24000

`ifndef DEPTH
    `define DEPTH 220
`endif

`ifndef DSR
    `define DSR 1
`endif

`ifndef OUT_FILE
    `define OUT_FILE results_cumul_fix
`endif

module TB_Cumulative_Fxp #() ();
    logic rst;
    logic clk;
    import Coefficients_Fx::*;

    localparam DownSampleDepth = $rtoi($ceil(`DEPTH / `DSR));
    localparam SampleWidth = N*`DSR; 

    // Instantiate common testbench objects
    logic[N-1:0] inSample;
    logic[`OUT_WIDTH-1:0] dutResult;
    logic isValid;
    TB_COM #(.N(N), .TestLength(`TestLength), .DSR(`DSR), .OUT_FILE(`STRINGIFY(`OUT_FILE))) com1 (.sample(inSample), .clk(clk), .rst(rst), .result(dutResult), .valid(isValid));

    localparam out_w = 14;

    // Instantiate DUTs
    Cumulative_Fxp #(.depth(`DEPTH), .DSR(`DSR), .n_mant(`MANT_W), .n_int(`EXP_W)) DUT ( .rst(rst), .clk(clk), .in(inSample), .out(dutResult), .valid(isValid));
    
    
    // Bind Modules to property checkers
    bind FxpPU FxpPU_prop #(.op(op), .n_int(n_int), .n_mant(n_mant)) flprop_i (.*);
    //bind FixLUT FixLUT_prop #(.size(size), .fact(fact)) lutprop_i (.*);
    //bind Batch_Fixed_top Batch_Fixed_prop #(.depth(`DEPTH), .DSR(`DSR), .n_int(n_int), .n_mant(n_mant)) batchprop_i (.*);

endmodule