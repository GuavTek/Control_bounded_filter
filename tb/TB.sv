//`define MANT_W 23
//`define EXP_W 8

`include "../sv/TopBatch.sv"
`include "../sv/Util.sv"
`include "../sv/FPU.sv"
`include "FPU_prop.sv"
`include "RAM_prop.sv"

`define TestLength 33536
`define N 3
`define T 4.167
`define VERBOSE_LVL 1

module TB #() ();
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
            if(`VERBOSE_LVL > 1)
                $display("Reading sample %b", inSample);
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
        static int fdo = $fopen("./Data/results.csv", "w");
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
//            $fwrite(fdo, "%b;\n", result);
            if (`VERBOSE_LVL > 1)
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
            #`T clk = ~clk;
        end
    end

    // define reset cycle
    initial begin
        rst = 0;
        repeat(5) @(posedge clk);
        rst = 1;
    end

    // Instantiate DUTs
    logic[`N-1:0] inDUT;
    assign inDUT = inSample;
    Batch_top #(.depth(192), .N(`N), .OSR(1)) DUT_Batch ( .rst(rst), .clk(clk), .in(inSample), .out(result));
    
    // Bind Modules to property checkers
    bind FPU FPU_prop #(.op(op)) flprop_i (.clk(clk), .*);  
    bind RAM_single RAM_single_prop #(.depth(depth), .d_width(d_width)) ramsprop_i (.*);
    bind RAM_dual RAM_dual_prop #(.depth(depth), .d_width(d_width)) ramdprop_i (.*);

endmodule