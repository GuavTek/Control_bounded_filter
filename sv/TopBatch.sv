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
    import Coefficients::*;

    localparam DownSampleDepth = $ceil(depth / OSR);

    // Counters for batch cycle
    logic[$clog2(depth)-1:0] batCount, batCountRev;      // counter for input samples
    always @(posedge clk) begin
        if(!rst || (batCount == (depth-1))) begin
            batCount = 0;
            batCountRev = depth-1;
        end else begin
            batCount++;
            batCountRev--;
        end
    end

    // Is low when the cycle is ending
    logic cyclePulse;
    assign cyclePulse = !(batCount == (depth-1));

    // Counter for cycles
    logic[$clog2(OSR)-1:0] osrCount;      // Prescale counter
    logic[$clog2(DownSampleDepth)-1:0] downBatCount, downBatCountRev;     // downsampled counters
    logic[1:0] cycle;
    logic sw1, sw2, sw3, sw4;   // Sample write signals
    always @(posedge clk) begin
        if(!rst) begin
            cycle = 0;
            osrCount = 0;
            downBatCount = 0;
            downBatCountRev = DownSampleDepth-1;
        end else if(!cyclePulse) begin
            cycle++;
            osrCount = 0;
            downBatCount = 0;
            downBatCountRev = DownSampleDepth-1;
        end else begin
            osrCount++;
            if (osrCount == OSR) begin
                downBatCountRev--;
                downBatCount++;
                osrCount = 0;
            end
        end

        sw1 = cycle == 2'd0;
        sw2 = cycle == 2'd1;
        sw3 = cycle == 2'd2;
        sw4 = cycle == 2'd3;    
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
    
    // Sample storage
    wire[N*OSR-1:0] sdf1, sdf2, sdf3, sdf4, sdff1, sdff2, sdff3, sdff4, sdr1, sdr2, sdr3, sdr4;
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
        end else begin
            always @(posedge clk) begin
                inShift = in;
            end
        end
    endgenerate

    // Sample multiplexing
    logic[N*OSR-1:0] slh, scob, sf_delay, scof;
    wire[3:0][N*OSR-1:0] slh_vec, sfd_vec, scob_vec;
    assign slh_vec = {sdf3, sdf2, sdf1, sdf4};
    assign sfd_vec = {sdf1, sdf4, sdf3, sdf2};
    assign scob_vec = {sdr1, sdr4, sdr3, sdr2};

    assign sdff1 = sw1 ? in : 'bZ;
    assign sdff2 = sw2 ? in : 'bZ;
    assign sdff3 = sw3 ? in : 'bZ;
    assign sdff4 = sw4 ? in : 'bZ;

    assign sdf1 = sdff1;
    assign sdf2 = sdff2;
    assign sdf3 = sdff3;
    assign sdf4 = sdff4;

    always @(posedge clkDS) begin
        scof = sf_delay;
        scob = scob_vec[cycle];
        sf_delay = sfd_vec[cycle];
        slh = slh_vec[cycle];
    end

    floatType res[N];

    genvar i;
    generate 
        for (i = 0; i < N ; i++ ) begin
            // Part-result storage
            wire[`MANT_W + `EXP_W:0] cf1, cf2, cb1, cb2, cff1, cff2, cbb1, cbb2;
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
            assign cff1 = cw1 ? resF.r : 'bZ;
            assign cff2 = cw2 ? resF.r : 'bZ;
            assign cbb1 = cw1 ? resB.r : 'bZ;
            assign cbb2 = cw2 ? resB.r : 'bZ;
            assign cf1 = cff1;
            assign cf2 = cff2;
            assign cb1 = cbb1;
            assign cb2 = cbb2;
            assign forward = cycle[0] ? cf2 : cf1;
            assign backward = cycle[0] ? cb2 : cb1;
            always @(*) begin
                if (cycle[0]) begin
                    cw1 = 1;
                    cw2 = 0;
                    baddr1 = downBatCountRev;
                    baddr2 = downBatCount;
                end else begin
                    cw1 = 0;
                    cw2 = 1;
                    baddr1 = downBatCount;
                    baddr2 = downBatCountRev;
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