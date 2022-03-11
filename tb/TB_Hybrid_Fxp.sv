`include "../sv/Hybrid_Fxp.sv"
`include "../sv/Util.sv"
`include "Util_TB.sv"
`include "TB_Common.sv"
`include "FxpPU_prop.sv"
//`include "LUT_Fxp_prop.sv"
//`include "TopFIRFix_prop.sv"

`define TestLength 24000

`ifndef DEPTH
    `define DEPTH 150
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
    `define OUT_FILE hybrid_fix
`endif

module TB_Hybrid_Fxp #() ();
    logic rst;
    logic clk;
    import Coefficients_Fx::*;

    // Instantiate common testbench objects
    logic[N-1:0] inSample;
    logic[`OUT_WIDTH-1:0] dutResult;
    logic isValid;
    TB_COM #(.N(N), .TestLength(`TestLength), .DSR(`DSR), .OUT_FILE(`STRINGIFY(`OUT_FILE))) com1 (.sample(inSample), .clk(clk), .rst(rst), .result(dutResult), .valid(isValid));

    // Instantiate DUT
    Hybrid_Fxp #(.depth(`DEPTH), .DSR(`DSR), .n_int(`EXP_W), .n_mant(`MANT_W)) DUT (
            .in(inSample), .rst(rst), .clk(clk), .out(dutResult), .valid(isValid)); 
    
    // Bind Modules to property checkers
    bind FxpPU FxpPU_prop #(.op(op), .n_int(n_int), .n_mant(n_mant)) flprop_i (.*);
    //bind LUT LUT_prop #(.size(size), .fact(fact)) lutprop_i (.*);
    //bind FIR_Fixed_top FIR_Fixed_prop #(.Lookahead(Lookahead), .Lookback(Lookback), .DSR(DSR)) firprop_i (.*);
    
    // Dump port waveforms for primetime
    `ifdef DUMP_PORT
        initial begin
            $dumpvars(1, DUT);
            $dumpfile("verilog.vcd");
        end
    `endif

endmodule