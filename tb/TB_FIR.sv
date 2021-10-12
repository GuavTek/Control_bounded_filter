`include "../sv/TopFIR.sv"
`include "../sv/Util.sv"
`include "../sv/FPU.sv"
`include "FPU_prop.sv"
`include "LUT_prop.sv"

`define TestLength 24000
`define N 3
`define T 4.167
`define Lookahead 100
`define Lookback 100
`define OSR 1
//`define VERBOSE_LVL 2

module TB_FIR #() ();
    logic rst;
    logic clk;

    // Read input file
    reg[`N-1:0] inSample = 0;
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
    floatType result;
    initial begin
        // Open output file
        static int fdo = $fopen("./Data/results_fir.csv", "w");
        if (!fdo) begin
            $error("File output was not opened");
            $stop;
        end

        // Wait for reset
        @(negedge rst);
        @(posedge rst);

        // Write data
        for (int i = 0; i < `TestLength; i++) begin
            $fwrite(fdo, "%f, ", ftor(result));
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
        rst = 0;
        repeat(2) @(posedge clk);
        rst = 1;
    end

    // Instantiate DUTs
    FIR_top #(.Lookahead(`Lookahead), .Lookback(`Lookback), .N(`N), .OSR(`OSR)) DUT_FIR (
            .in(inSample), .rst(rst), .clk(clk), .out(result)); 
    
    
    // Bind Modules to property checkers
    bind FPU FPU_prop #(.op(op)) flprop_i (.*);
    bind LUT LUT_prop #(.size(size), .fact(fact)) lutprop_i (.*);

endmodule