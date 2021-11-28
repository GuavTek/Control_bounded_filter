`include "../sv/Data/Coefficients.sv"
`include "../sv/TopBatch.sv"
`include "../sv/Util.sv"
`include "Util_TB.sv"
`include "../sv/FPU.sv"
`include "FPU_prop.sv"
`include "RAM_prop.sv"
`include "LUT_prop.sv"
`include "RecursionModule_prop.sv"
`include "TopBatch_prop.sv"

`ifndef DEPTH
    `define DEPTH 220
`endif

`ifndef OSR
    `define OSR 1
`endif

`ifndef VERBOSE_LVL
    `define VERBOSE_LVL 2
`endif

`ifndef OUT_FILE
    `define OUT_FILE results_batch
`endif

`define TestLength 24000
`define T 4.167

module TB_BATCH #() ();
    logic rst = 1;
    logic clk;
    import Coefficients::*;

    localparam DownSampleDepth = $rtoi($ceil(`DEPTH / `OSR));
    localparam SampleWidth = N*`OSR; 

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
    floatType result;
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
        repeat(4) @(posedge clk);
        rst = 0;
        repeat(2*`OSR + 1) @(posedge clk);
        rst = 1;
    end

    // Instantiate DUTs
    logic[SampleWidth-1:0] sampleDataOut1, sampleDataOut2, sampleDataOut3, sampleDataIn;
    logic[$clog2(4*DownSampleDepth)-1:0] sampleAddrIn, sampleAddrOut1, sampleAddrOut2, sampleAddrOut3;
    floatType resDataInB, resDataInF, resDataOutB, resDataOutF;
    logic[$clog2(2*DownSampleDepth)-1:0] resAddrInB, resAddrInF, resAddrOutB, resAddrOutF;
    logic sampleClk, resClkF, resClkB, sampleWrite, resWriteB, resWriteF;
    RAM_triple #(.depth(4*DownSampleDepth), .d_width(SampleWidth)) sample (.clk(sampleClk), .rst(rst), .write(sampleWrite), .dataIn(sampleDataIn), .addrIn(sampleAddrIn), 
            .dataOut1(sampleDataOut1), .dataOut2(sampleDataOut2), .dataOut3(sampleDataOut3), .addrOut1(sampleAddrOut1), .addrOut2(sampleAddrOut2), .addrOut3(sampleAddrOut3));

    RAM_single #(.depth(2*DownSampleDepth), .d_width((`EXP_W + `MANT_W)+1)) calcB (.clk(resClkB), .rst(rst), .write(resWriteB), .dataIn(resDataInB), .addrIn(resAddrInB),
            .dataOut(resDataOutB), .addrOut(resAddrOutB));
    RAM_single #(.depth(2*DownSampleDepth), .d_width((`EXP_W + `MANT_W)+1)) calcF (.clk(resClkF), .rst(rst), .write(resWriteF), .dataIn(resDataInF), .addrIn(resAddrInF),
            .dataOut(resDataOutF), .addrOut(resAddrOutF));

    Batch_top #(.depth(`DEPTH), .OSR(`OSR)) DUT_Batch ( .rst(rst), .clk(clk), .in(inSample), .out(result),
    .sampleAddrIn(sampleAddrIn), .sampleAddrOut1(sampleAddrOut1), .sampleAddrOut2(sampleAddrOut2), .sampleAddrOut3(sampleAddrOut3),
	.sampleClk(sampleClk), .sampleWrite(sampleWrite), .sampleDataIn(sampleDataIn),
	.sampleDataOut1(sampleDataOut1), .sampleDataOut2(sampleDataOut2), .sampleDataOut3(sampleDataOut3),
    .resAddrInF(resAddrInF), .resAddrInB(resAddrInB), .resAddrOutF(resAddrOutF), .resAddrOutB(resAddrOutB),
	.resClkF(resClkF), .resClkB(resClkB), .resWriteF(resWriteF), .resWriteB(resWriteB),
	.resDataInF(resDataInF), .resDataInB(resDataInB), .resDataOutF(resDataOutF), .resDataOutB(resDataOutB));
    
    // Bind Modules to property checkers
    bind FPU FPU_prop #(.op(op)) flprop_i (.*);  
    bind RAM_single RAM_single_prop #(.depth(depth), .d_width(d_width)) ramsprop_i (.rst(rst), .*);
    bind RAM_triple RAM_triple_prop #(.depth(depth), .d_width(d_width)) ramtprop_i (.*);
    bind LUT LUT_prop #(.size(size), .fact(fact)) lutprop_i (.*);
    bind RecursionModule RecursionModule_prop #(.factorR(factorR), .factorI(factorI)) Recprop_i (.*);
    bind Batch_top Batch_top_prop #(.depth(depth), .OSR(OSR)) batchprop_i (.*);

endmodule