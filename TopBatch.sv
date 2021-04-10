`include "Util.sv"
`include "FPU.sv"
`include "CFPU.sv"
`include "RecursionModule.sv"
`include "LUT.sv"
`include "RAM.sv"
`include "Data/Coefficients.v"

module Batch_top #(
    parameter depth = 32,
    parameter width = 32,
    parameter N = 3
) (
    input logic [N-1:0] in,
    input logic rst, clk,
    output floatType out
);
    // Counter for batch cycle
    logic[$clog2(depth)-1:0] batCount, batCountRev;
    always @(posedge clk) begin
        if(batCount == (depth-1)) begin
            batCount = 0;
            batCountRev = depth-1;
        end else begin
            batCount++;
            batCountRev--;
        end
    end

    logic cyclePulse;
    assign cyclePulse = !(batCount == (depth-1));

    // Counter for cycles
    logic[1:0] cycle;
    always @(posedge clk) begin
        if(batCount == (depth-1))
            cycle++;
    end
    
    // Sample storage
    logic[N-1:0] sdf1, sdf2, sdf3, sdf4, sdr1, sdr2, sdr3, sdr4;
    logic sw1, sw2, sw3, sw4;
    RAM_dual #(.depth(depth), .d_width(N)) sample1 (.clk(clk), .data1(sdf1), .write1(sw1), .addr1(batCount), .data2(sdr1), .addr2(batCountRev));
    RAM_dual #(.depth(depth), .d_width(N)) sample2 (.clk(clk), .data1(sdf2), .write1(sw2), .addr1(batCount), .data2(sdr2), .addr2(batCountRev));
    RAM_dual #(.depth(depth), .d_width(N)) sample3 (.clk(clk), .data1(sdf3), .write1(sw3), .addr1(batCount), .data2(sdr3), .addr2(batCountRev));
    RAM_dual #(.depth(depth), .d_width(N)) sample4 (.clk(clk), .data1(sdf4), .write1(sw4), .addr1(batCount), .data2(sdr4), .addr2(batCountRev));

    // Sample multiplexing
    logic[N-1:0] slh, scof, scob, sf_delay;
    always @(*) begin
        case (cycle)
            2'd0:
            begin
                sw1 = 1;
                sw2 = 0;
                sw3 = 0;
                sw4 = 0;
                sdf1 = in;
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
                slh = sdf3;
                sf_delay = sdf1;
                scob = sdr1;
            end 
        endcase
    end

    always @(posedge clk) begin
        scof = sf_delay;
    end

    floatType res[N];

    genvar i;
    generate 
        for (i = 0; i < N ; i++ ) begin
            // Part-result storage
            floatType cf1, cf2, cb1, cb2;
            logic cw1, cw2;
            logic[$clog2(depth)-1:0] baddr1, baddr2;
            RAM_single #(.depth(depth), .d_width($bits(res[0]))) calcF1 (.clk(clk), .data(cf1), .write(cw1), .addr(batCount));
            RAM_single #(.depth(depth), .d_width($bits(res[0]))) calcF2 (.clk(clk), .data(cf2), .write(cw2), .addr(batCount));
            RAM_single #(.depth(depth), .d_width($bits(res[0]))) calcB1 (.clk(clk), .data(cb1), .write(cw1), .addr(baddr1));
            RAM_single #(.depth(depth), .d_width($bits(res[0]))) calcB2 (.clk(clk), .data(cb2), .write(cw2), .addr(baddr2));

            // Lookahead
            complex LH_res, LH_in;
            LUT #(.size(N), .re(Fbr[i][N-1:0]), .im(Fbi[i][N-1:0])) LHL_ (.sel(slh), .result(LH_in));
            RecursionModule #(.factorR(Lbr[i]), .factorI(Lbi[i])) LHR_ (.in(LH_in), .rst(cyclePulse & rst), .resetVal(0), .clk(clk), .out(LH_res));

            // Compute
            complex CF_in, CB_in, CF_out, CB_out, WF, WB;
            LUT #(.size(N), .re(Ffr[i][N-1:0]), .im(Ffi[i][N-1:0])) CFL_ (.sel(scof), .result(CF_in));
            LUT #(.size(N), .re(Fbr[i][N-1:0]), .im(Fbi[i][N-1:0])) CBL_ (.sel(scob), .result(CB_in));
            RecursionModule #(.factorR(Lfr[i]), .factorI(Lfi[i])) CFR_ (.in(CF_in), .rst(rst), .resetVal(0), .clk(clk), .out(CF_out));
            RecursionModule #(.factorR(Lbr[i]), .factorI(Lbi[i])) CBR_ (.in(CB_in), .rst(cyclePulse & rst), .resetVal(LH_res), .clk(clk), .out(CB_out));
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
                    baddr1 = batCountRev;
                    baddr2 = batCount;
                    cf1 = resF.r;
                    cb1 = resB.r;
                    forward = cf2;
                    backward = cb2;
                end else begin
                    cw1 = 0;
                    cw2 = 1;
                    baddr1 = batCount;
                    baddr2 = batCountRev;
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