`include "Util_TB.sv"

`ifndef CLK_FREQ
    `define CLK_FREQ 240e6
`endif

// Clock period (ns)
`ifndef T
    `define T 1.0e9/`CLK_FREQ
`endif

`ifndef VERBOSE_LVL
    `define VERBOSE_LVL 2
`endif

module TB_COM #(
    parameter TestLength = 24000,
    parameter DSR = 12,
    parameter N = 4, M = N,
    parameter string OUT_FILE = "results"
) (
    sample,
    clk,
    rst,
    result,
    valid
);
    
    output logic[N-1:0] sample;
    output logic clk, rst;
    input logic[`OUT_WIDTH-1:0] result;
    input logic valid;

    // Read stimuli
    initial begin
        // Open input file
        static int fdi;
        automatic string stim_file;
        $sformat(stim_file, "./Data/verilog_signals_%1dN%1dM_F%0d.csv", N, M, int'(`CLK_FREQ/1e6));
        fdi = $fopen(stim_file, "r");
        if (!fdi) begin 
            $error("File input was not opened");
            $stop;
        end
        
        // Prepare first sample
        void'($fscanf(fdi, "%b,\n", sample));

        // Wait for reset cycle
        @(negedge rst);
        @(negedge rst);
        @(posedge rst);

        if(`VERBOSE_LVL > 0)
            $display("Start reading samples");

        // Read until end of file
        while ($fscanf(fdi, "%b,\n", sample) > 0) begin
            // Wait for clock cycle
            if(`VERBOSE_LVL > 2)
                $display("Reading sample %b as %d", sample, sample);
            @(posedge clk);
        end

        if(`VERBOSE_LVL > 0)
            $display("Done reading samples");
        // Close file
        $fclose(fdi);
        
    end

    // Write results
    logic signed[`OUT_WIDTH-1:0] signedResult;
    initial begin
        // Open output file
        static string file_path = {"./results/", OUT_FILE, ".csv"};
        static int fdo = $fopen(file_path, "w");
        if (!fdo) begin
            $error("File output was not opened");
            $stop;
        end

        // Wait for reset
        @(negedge rst);
        @(negedge rst);
        @(posedge rst);

        // Wait for valid data from dut
        @(posedge valid);

        $display("Start writing results");

        // Write data
        for (int i = 0; i < TestLength; i++) begin
            // Write only one in DSR number of results
            if (i % DSR) begin 
                @(posedge clk);
                continue;
            end

            signedResult = {~result[`OUT_WIDTH-1], result[`OUT_WIDTH-2:0]};
            $fwrite(fdo, "%0d, ", signedResult);
            //$fwrite(fdo, "%b;\n", result);
            if (`VERBOSE_LVL > 2)
                $display("Write result %d.\n", i);

            @(posedge clk);
        end

        $display("Done writing results");

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
        repeat(DSR*2) @(posedge clk);
        rst = 0;
        repeat(DSR*2) @(posedge clk);
        rst = 1;
        repeat(DSR*2) @(posedge clk);
        rst = 0;
        repeat(DSR*2) @(posedge clk);
        rst = 1;
    end

endmodule