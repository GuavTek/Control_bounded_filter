`include "../sv/TopHybridFix.sv"
`include "../sv/Util.sv"
`include "Util_TB.sv"
`include "TB_Common.sv"
`include "FixPU_prop.sv"
//`include "LUT_prop.sv"
//`include "TopFIRFix_prop.sv"

`include "../sv/Data/Coefficients_Fixedpoint.sv"
`define TestLength 24000

`ifndef DEPTH
    `define DEPTH 150
`endif

`ifndef OSR1
    `define OSR1 2
`endif

`ifndef OSR2
    `define OSR2 6
`endif

`ifndef OSR
    `define OSR (`OSR1 * `OSR2)
`endif

`ifndef OUT_FILE
    `define OUT_FILE hybrid_fix
`endif

module TB_HYBRID_Fixed #() ();
    logic rst;
    logic clk;
    import Coefficients_Fx::*;

    // Instantiate common testbench objects
    logic[N-1:0] inSample;
    logic[`OUT_WIDTH-1:0] dutResult;
    logic isValid;
    TB_COM #(.N(N), .TestLength(`TestLength), .OSR(`OSR), .OUT_FILE(`STRINGIFY(`OUT_FILE))) com1 (.sample(inSample), .clk(clk), .rst(rst), .result(dutResult), .valid(isValid));

    // Instantiate DUT
    Hybrid_Fixed_top #(.depth(`DEPTH), .OSR(`OSR), .n_int(`EXP_W), .n_mant(`MANT_W)) DUT_HYBRID (
            .in(inSample), .rst(rst), .clk(clk), .out(dutResult), .valid(isValid)); 
    
    // Bind Modules to property checkers
    bind FixPU FixPU_prop #(.op(op), .n_int(n_int), .n_mant(n_mant)) flprop_i (.*);
    //bind LUT LUT_prop #(.size(size), .fact(fact)) lutprop_i (.*);
    //bind FIR_Fixed_top FIR_Fixed_prop #(.Lookahead(Lookahead), .Lookback(Lookback), .OSR(OSR)) firprop_i (.*);

endmodule