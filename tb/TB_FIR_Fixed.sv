`include "../sv/TopFIRFix.sv"
`include "../sv/Util.sv"
`include "Util_TB.sv"
`include "TB_Common.sv"
`include "FixPU_prop.sv"
//`include "FPU_prop.sv"
//`include "LUT_prop.sv"
//`include "TopFIRFix_prop.sv"

`include "../sv/Data/Coefficients_Fixedpoint.sv"
`define TestLength 24000

`ifndef DEPTH
    `define DEPTH 220
`endif

`ifndef LOOKAHEAD
    `define LOOKAHEAD `DEPTH
`endif

`ifndef LOOKBACK
    `define LOOKBACK `DEPTH
`endif

`ifndef DSR
    `define DSR 1
`endif

`ifndef OUT_FILE
    `define OUT_FILE results_fir_fix
`endif

module TB_FIR_Fixed #() ();
    logic rst;
    logic clk;
    import Coefficients_Fx::*;

    // Instantiate common testbench objects
    logic[N-1:0] inSample;
    logic[`OUT_WIDTH-1:0] dutResult;
    logic isValid;
    TB_COM #(.N(N), .TestLength(`TestLength), .DSR(`DSR), .OUT_FILE(`STRINGIFY(`OUT_FILE))) com1 (.sample(inSample), .clk(clk), .rst(rst), .result(dutResult), .valid(isValid));
    

    // Instantiate DUTs
    FIR_Fixed_top #(.Lookahead(`LOOKAHEAD), .Lookback(`LOOKBACK), .DSR(`DSR), .n_int(`EXP_W), .n_mant(`MANT_W)) DUT_FIR (
            .in(inSample), .rst(rst), .clk(clk), .out(dutResult), .valid(isValid)); 
    
    
    // Bind Modules to property checkers
    bind FixPU FixPU_prop #(.op(op), .n_int(n_int), .n_mant(n_mant)) flprop_i (.*);
    //bind LUT LUT_prop #(.size(size), .fact(fact)) lutprop_i (.*);
    //bind FIR_Fixed_top FIR_Fixed_prop #(.Lookahead(Lookahead), .Lookback(Lookback), .DSR(DSR)) firprop_i (.*);

endmodule