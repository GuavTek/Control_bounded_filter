`include "Util.sv"
`include "Data/Coefficients.v"
//`include "FPU.sv"
//`include "CFPU.sv"
//`include "RecursionModule.sv"
//`include "LUT.sv"
//`include "RAM.sv"

module Batch_top #(
    parameter depth = 32,
    parameter N = 3,
    parameter OSR = 2
) (
    input logic [N-1:0] in,
    input logic rst, clk,
    output floatType out
);

    localparam DownSampleDepth = $ceil(depth / OSR);

    // Counters for batch cycle
    logic[$clog2(depth)-1:0] batCount, batCountRev;      // counter for input samples
    logic[$clog2(OSR)-1:0] osrCount;      // Prescale counter
    logic[$clog2(DownSampleDepth)-1:0] downBatCount, downBatCountRev;     // downsampled counters
    always @(posedge clk) begin
        if(batCount == (depth-1)) begin
            batCount = 0;
            batCountRev = depth-1;
            downBatCount = 0;
            downBatCountRev = DownSampleDepth-1;
            osrCount = 0;
        end else begin
            batCount++;
            batCountRev--;
            osrCount++;
            if (osrCount == OSR) begin
                downBatCountRev--;
                downBatCount++;
                osrCount = 0;
            end
        end
    end

    // Downsampled clock
    logic clkDS;
    generate
        if(OSR > 1) begin
            // MSb of counter is prescaled clock, not symmetrical for all OSR
            // Rising edge when osrCount = 0
            assign clkDS = !osrCount[$clog2(OSR)-1];
        end else begin
            assign clkDS = clk;
        end
    endgenerate
    

    // Is low when the cycle is ending
    logic cyclePulse;
    assign cyclePulse = !(batCount == (depth-1));

    // Counter for cycles
    logic[1:0] cycle;
    always @(posedge clk) begin
        if(!cyclePulse)
            cycle++;
    end
    
    // Sample storage
    logic[N*OSR-1:0] sdf1, sdf2, sdf3, sdf4, sdr1, sdr2, sdr3, sdr4;
    logic sw1, sw2, sw3, sw4;
    RAM_dual #(.depth(DownSampleDepth), .d_width(N*OSR)) sample1 (.clk(clkDS), .data1(sdf1), .write1(sw1), .addr1(downBatCount), .data2(sdr1), .addr2(downBatCountRev));
    RAM_dual #(.depth(DownSampleDepth), .d_width(N*OSR)) sample2 (.clk(clkDS), .data1(sdf2), .write1(sw2), .addr1(downBatCount), .data2(sdr2), .addr2(downBatCountRev));
    RAM_dual #(.depth(DownSampleDepth), .d_width(N*OSR)) sample3 (.clk(clkDS), .data1(sdf3), .write1(sw3), .addr1(downBatCount), .data2(sdr3), .addr2(downBatCountRev));
    RAM_dual #(.depth(DownSampleDepth), .d_width(N*OSR)) sample4 (.clk(clkDS), .data1(sdf4), .write1(sw4), .addr1(downBatCount), .data2(sdr4), .addr2(downBatCountRev));


    // Shifted input
    logic[N*OSR-1:0] inShift;

    // Generates shift register if OSR > 1
    generate
        if (OSR > 1) begin
            always @(posedge clk) begin
                inShift[N*OSR-1:N] = inShift[N*OSR-N-1:0];
                inShift[N-1:0] = in;
            end
        end else
            assign inShift = in;
    endgenerate

    // Sample multiplexing
    logic[N*OSR-1:0] slh, scof, scob, sf_delay;
    always @(*) begin
        case (cycle)
            2'd0:
            begin
                sw1 = 1;
                sw2 = 0;
                sw3 = 0;
                sw4 = 0;
                sdf1 = in;
                sdf3 = 'bZ;
                slh = sdf4;
                sf_delay = sdf2;
                scob = sdr2;
            end
            2'd1:
            begin
                sw1 = 0;
                sw2 = 1;
                sw3 = 0;
                sw4 = 0;
                sdf2 = in;
                sdf4 = 'bZ;
                slh = sdf1;
                sf_delay = sdf3;
                scob = sdr3;
            end
            2'd2:
            begin
                sw1 = 0;
                sw2 = 0;
                sw3 = 1;
                sw4 = 0;
                sdf3 = in;
                sdf1 = 'bZ;
                slh = sdf2;
                sf_delay = sdf4;
                scob = sdr4;
            end
            2'd3:
            begin
                sw1 = 0;
                sw2 = 0;
                sw3 = 0;
                sw4 = 1;
                sdf4 = in;
                sdf2 = 'bZ;
                slh = sdf3;
                sf_delay = sdf1;
                scob = sdr1;
            end 
        endcase
    end

    always @(posedge clkDS) begin
        scof = sf_delay;
    end

    floatType res[N];

    genvar i;
    generate 
        for (i = 0; i < N ; i++ ) begin
            // Part-result storage
            floatType cf1, cf2, cb1, cb2;
            logic cw1, cw2;
            logic[$clog2(DownSampleDepth)-1:0] baddr1, baddr2;
            RAM_single #(.depth(DownSampleDepth), .d_width($bits(res[0]))) calcF1 (.clk(clkDS), .data(cf1), .write(cw1), .addr(downBatCount));
            RAM_single #(.depth(DownSampleDepth), .d_width($bits(res[0]))) calcF2 (.clk(clkDS), .data(cf2), .write(cw2), .addr(downBatCount));
            RAM_single #(.depth(DownSampleDepth), .d_width($bits(res[0]))) calcB1 (.clk(clkDS), .data(cb1), .write(cw1), .addr(baddr1));
            RAM_single #(.depth(DownSampleDepth), .d_width($bits(res[0]))) calcB2 (.clk(clkDS), .data(cb2), .write(cw2), .addr(baddr2));

            // Lookahead
            complex LH_res, LH_in;
            LUT #(.size(N*OSR), .re(Fbr[i][0:N*OSR-1]), .im(Fbi[i][0:N*OSR-1])) LHL_ (.sel(slh), .result(LH_in));
            RecursionModule #(.factorR(Lbr[i]**OSR), .factorI(Lbi[i]**OSR)) LHR_ (.in(LH_in), .rst(cyclePulse & rst), .resetVal(LH_in), .clk(clkDS), .out(LH_res));

            // Compute
            complex CF_in, CB_in, CF_out, CB_out, WF, WB;
            LUT #(.size(N*OSR), .re(Ffr[i][0:N*OSR-1]), .im(Ffi[i][0:N*OSR-1])) CFL_ (.sel(scof), .result(CF_in));
            LUT #(.size(N*OSR), .re(Fbr[i][0:N*OSR-1]), .im(Fbi[i][0:N*OSR-1])) CBL_ (.sel(scob), .result(CB_in));
            RecursionModule #(.factorR(Lfr[i]**OSR), .factorI(Lfi[i]**OSR)) CFR_ (.in(CF_in), .rst(rst), .resetVal(CF_in), .clk(clkDS), .out(CF_out));
            RecursionModule #(.factorR(Lbr[i]**OSR), .factorI(Lbi[i]**OSR)) CBR_ (.in(CB_in), .rst(cyclePulse & rst), .resetVal(LH_res), .clk(clkDS), .out(CB_out));
            assign WF.r = rtof(Wfr[i]);
            assign WF.i = rtof(Wfi[i]);
            assign WB.r = rtof(Wbr[i]);
            assign WB.i = rtof(Wbi[i]);
            complex resF, resB;
            CFPU #(.op(MULT)) WFR_ (.A(CF_out), .B(WF), .result(resF));
            CFPU #(.op(MULT)) WBR_ (.A(CB_out), .B(WB), .result(resB));

            // Final add
            floatType forward, backward, partRes;
            FPU #(.op(ADD)) PRes_ (.A(forward), .B(backward), .result(partRes));
            
            // MUX Part-results
            always @(*) begin
                if (cycle[0]) begin
                    cw1 = 1;
                    cw2 = 0;
                    baddr1 = downBatCountRev;
                    baddr2 = downBatCount;
                    cf1 = resF.r;
                    cb1 = resB.r;
                    forward = cf2;
                    backward = cb2;
                end else begin
                    cw1 = 0;
                    cw2 = 1;
                    baddr1 = downBatCount;
                    baddr2 = downBatCountRev;
                    cf2 = resF.r;
                    cb2 = resB.r;
                    forward = cf1;
                    backward = cb1;
                end
            end

            if(i == 0) begin
                assign res[0] = partRes;
            end else begin
                FPU #(.op(ADD)) FINADD (.A(res[i-1]), .B(partRes), .result(res[i]));
            end
        end
    endgenerate

    // Final final result
    assign out = res[N-1];
endmodule