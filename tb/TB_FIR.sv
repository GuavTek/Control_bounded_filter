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
`include "FPU_prop.sv"
`include "LUT_prop.sv"
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

`ifndef DSR
    `define DSR 1
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
    TB_COM #(.N(N), .TestLength(`TestLength), .DSR(`DSR), .OUT_FILE(`STRINGIFY(`OUT_FILE))) com1 (.sample(inSample), .clk(clk), .rst(rst), .result(dutResult), .valid(isValid));

    // Instantiate DUTs
    FIR_top #(.Lookahead(`LOOKAHEAD), .Lookback(`LOOKBACK), .DSR(`DSR), .n_exp(`EXP_W), .n_mant(`MANT_W)) DUT_FIR (
            .in(inSample), .rst(rst), .clk(clk), .out(dutResult), .valid(isValid)); 
    
    // dummy type (so compiler knows there is a datatype with this name)
    typedef struct packed { 
        logic dum;
    } float_t;

    // Bind Modules to property checkers
    bind FPU FPU_prop #(.op(op), .n_exp(n_exp), .n_mant(n_mant), .float_t(float_t)) flprop_i (.*);
    bind LUT LUT_prop #(.size(size), .fact(fact), .n_mant(n_mant), .n_int(n_int), .f_exp(f_exp), .f_mant(f_mant), .float_t(float_t)) lutprop_i (.*);
    //bind FIR_top FIR_prop #(.Lookahead(Lookahead), .Lookback(Lookback), .DSR(DSR)) firprop_i (.*);

endmodule