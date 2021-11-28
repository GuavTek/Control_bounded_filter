`include "Util_TB.sv"
`include "../sv/TopFIR.sv"
`include "../sv/Util.sv"
`include "../sv/FPU.sv"
`include "FPU_prop.sv"
`include "LUT_prop.sv"
`include "TopFIR_prop.sv"

`include "../sv/Data/Coefficients.sv"
`define TestLength 24000
//`define N 3
`define T 4.167

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

`ifndef VERBOSE_LVL
    `define VERBOSE_LVL 2
`endif

`ifndef OUT_FILE
    `define OUT_FILE results_fir
`endif

module TB_FIR #() ();
    logic rst;
    logic clk;
    import Coefficients::*;

    // Read input file
    reg[N-1:0] inSample = 0;
    initial begin
        // Open input file
        static int fdi = $fopen("./Data/verilog_signals.csv", "r");
        if (!fdi) begin 
            $error("File input was not opened");
            $stop;
        end
        
        // Prepare first sample
        $fscanf(fdi, "%b,\n", inSample);

        // Wait for reset cycle
        @(negedge rst);
        @(posedge rst);

        if(`VERBOSE_LVL > 0)
            $display("Start reading samples");

        // Read until end of file
        while ($fscanf(fdi, "%b,\n", inSample) > 0) begin
            // Wait for clock cycle
            if(`VERBOSE_LVL > 2)
                $display("Reading sample %b as %d", inSample, inSample);
            @(posedge clk);
        end

        if(`VERBOSE_LVL > 0)
            $display("Done reading samples");
        // Close file
        $fclose(fdi);
        
    end

    // Write output file
    floatType dutResult;
    initial begin
        // Open output file
        static string file_path = {"./Data/", `STRINGIFY(`OUT_FILE), ".csv"};
        static int fdo = $fopen(file_path, "w");
        if (!fdo) begin
            $error("File output was not opened");
            $stop;
        end

        // Wait for reset
        @(negedge rst);
        @(posedge rst);

        // Write data
        for (int i = 0; i < `TestLength; i++) begin
            // Write only one in OSR number of results
            if (i % `OSR) begin 
                @(posedge clk);
                continue;
            end
            $fwrite(fdo, "%f, ", ftor(dutResult));
            //$fwrite(fdo, "%b;\n", result);
            if (`VERBOSE_LVL > 2)
                $display("Write result %d.\n", i);
            @(posedge clk);
        end

        // Close file
        $fclose(fdo);
        
        // End simulation
        $finish;
    end
    
    // Define clock
    initial begin
        clk = 1;
        forever begin
            #(`T/2) clk = ~clk;
        end
    end

    // define reset cycle
    initial begin
        rst = 1;
        repeat(4) @(posedge clk);
        rst = 0;
        repeat(`OSR+1) @(posedge clk);
        rst = 1;
    end

    // Instantiate DUTs
    FIR_top #(.Lookahead(`LOOKAHEAD), .Lookback(`LOOKBACK), .OSR(`OSR)) DUT_FIR (
            .in(inSample), .rst(rst), .clk(clk), .out(dutResult)); 
    
    
    // Bind Modules to property checkers
    bind FPU FPU_prop #(.op(op)) flprop_i (.*);
    bind LUT LUT_prop #(.size(size), .fact(fact)) lutprop_i (.*);
    bind FIR_top FIR_prop #(.Lookahead(Lookahead), .Lookback(Lookback), .OSR(OSR)) firprop_i (.*);

endmodule