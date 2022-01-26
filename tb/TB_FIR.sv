`include "HardFloat-1/source/HardFloat_consts.vi"
`include "HardFloat-1/source/HardFloat_specialize.vi"
`include "HardFloat-1/source/HardFloat_primitives.v"
`include "HardFloat-1/source/isSigNaNRecFN.v"
`include "HardFloat-1/source/HardFloat_rawFN.v"
`include "HardFloat-1/source/fNToRecFN.v"
`include "HardFloat-1/source/recFNToFN.v"
`include "HardFloat-1/source/addRecFN.v"
`include "HardFloat-1/source/mulRecFN.v"

`include "../sv/TopFIR.sv"
`include "../sv/Util.sv"
`include "../sv/FPU.sv"
`include "Util_TB.sv"
`include "TB_Common.sv"
//`include "FPU_prop.sv"
//`include "LUT_prop.sv"
//`include "TopFIR_prop.sv"

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

`ifndef OSR
`define OSR 1
`endif

`ifndef OUT_FILE
    `define OUT_FILE results_fir
`endif

module TB_FIR #() ();
    logic rst;
    logic clk;
    import Coefficients_Fx::*;

    // Instantiate common testbench objects
    logic[N-1:0] inSample;
    logic[`OUT_WIDTH-1:0] dutResult;
    logic isValid;
    TB_COM #(.N(N), .TestLength(`TestLength), .OSR(`OSR), .OUT_FILE(`STRINGIFY(`OUT_FILE))) com1 (.sample(inSample), .clk(clk), .rst(rst), .result(dutResult), .valid(isValid));

    // Instantiate DUTs
    FIR_top #(.Lookahead(`LOOKAHEAD), .Lookback(`LOOKBACK), .OSR(`OSR), .n_exp(`EXP_W), .n_mant(`MANT_W)) DUT_FIR (
            .in(inSample), .rst(rst), .clk(clk), .out(dutResult), .valid(isValid)); 
    
    // Bind Modules to property checkers
    //bind FPU FPU_prop flprop_i (.*);
    //bind LUT LUT_prop #(.size(size), .fact(fact)) lutprop_i (.*);
    //bind FIR_top FIR_prop #(.Lookahead(Lookahead), .Lookback(Lookback), .OSR(OSR)) firprop_i (.*);

endmodule