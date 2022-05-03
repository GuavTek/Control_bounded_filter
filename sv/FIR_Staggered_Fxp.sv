`ifndef FIR_FXP_SV_
`define FIR_FXP_SV_

`include "Util.sv"
`include "FxpPU.sv"
`include "LUT_Fxp.sv"
`include "Fxp_To_Fxp.sv"
`include "ClkDiv.sv"
`include "ValidCount.sv"
`include "InputReg.sv"

`define MAX_LUT_SIZE 4
`define COMB_ADDERS 3
`define OUT_WIDTH 12

module FIR_Staggered_Fxp #(
    parameter Lookahead = 96,
    parameter Lookback = 96,
    parameter DSR = 6,
    parameter Stagger = 2,
    parameter n_int = 0,
    parameter n_mant = 14
) ( 
    in, rst, clk, out, valid
);
    import Coefficients_Fx::N;
    import Coefficients_Fx::M;
    
    input wire [M-1:0] in;
    input logic rst, clk;
    output logic[`OUT_WIDTH-1:0] out;
    output logic valid;

    localparam Looktotal = Lookahead + Lookback + DSR*(Stagger-1);
    localparam int LookaheadLUTs = $ceil((0.0 + M*Lookahead)/`MAX_LUT_SIZE);
    localparam int LookbackLUTs = $ceil((0.0 + M*Lookback)/`MAX_LUT_SIZE);
    localparam int AddersNum = LookbackLUTs + LookaheadLUTs;
    localparam AdderLayers = $clog2(AddersNum);
    localparam n_tot = n_int + n_mant;
    localparam StaggerWidth = M*DSR*Stagger;

    // Downsampled clock
    logic[$clog2(DSR*Stagger)-1:0] divCnt1;
    logic[$clog2(DSR)-1:0] divCnt2;
    logic clkDS, clkOut;
    ClkDiv #(.DSR(DSR*Stagger)) ClkDivider1 (.clkIn(clk), .rst(rst), .clkOut(clkDS), .cntOut(divCnt1));
    ClkDiv #(.DSR(DSR)) ClkDivider2 (.clkIn(clk), .rst(rst), .clkOut(clkOut), .cntOut(divCnt2));
    

    // Data valid counter
    localparam int validTime = $ceil((0.0 + Looktotal)/(DSR*Stagger)) + $ceil((0.0 + AdderLayers)/(`COMB_ADDERS + 1)) + 3;
    logic dummyValid;
    ValidCount #(.TopVal(validTime)) vc1 (.clk(clkDS), .rst(rst), .out(valid), .out2(dummyValid));

    // Input register
    logic [StaggerWidth-1:0] inSample;
    generate
        if(DSR*Stagger > 1) begin
            if(Stagger > 1) begin
                logic [DSR*M-1:0] tempSample;
                always @(posedge clk) begin
                    tempSample <= {tempSample[0 +: M*DSR-M], in};
                end

                always @(posedge clkOut) begin
                    inSample <= {inSample[0 +: StaggerWidth-M*DSR], tempSample};
                end
            end else begin
                always @(posedge clk) begin
                    inSample <= {inSample[0 +: StaggerWidth-M], in};
                end
            end
        end else begin
            always @(posedge clk) begin
                inSample <= in;
            end
        end
    endgenerate

    // Sample shift-register
    logic[M*Looktotal-1:0] inShift;
    always @(posedge clkDS) begin
        inShift <= {inShift[0 +: M*Looktotal-StaggerWidth], inSample};
    end

    // Prepare lookback samples
    logic[M*Lookback+M*DSR*(Stagger-1)-1:0] sampleback;
    assign sampleback = inShift[M*Looktotal-1:M*Lookahead];

    // Prepare lookahead samples
    logic[M*Lookahead+M*DSR*(Stagger-1)-1:0] sampleahead;
    generate
        // Invert sample-order
        for(genvar i = 0; i < Lookahead + DSR*(Stagger-1); i++) begin
            assign sampleahead[M*i +: M] = inShift[M*(Lookahead+DSR*(Stagger-1)-i-1) +: M];
        end
    endgenerate


    // Load constants
    GetHb #(.n_int(n_int), .n_mant(n_mant), .size(M*Lookahead)) hb_slice ();
    GetHf #(.n_int(n_int), .n_mant(n_mant), .size(M*Lookback)) hf_slice ();
    
    // Generate LUTs
    logic signed[n_tot:0] totResult[Stagger-1:0];
    generate
        for (genvar i = 0; i < Stagger ; i++ ) begin
            logic signed[n_tot:0] lookaheadResult;
            logic signed[n_tot:0] lookbackResult;
            // Calculate lookahead
            LUT_Unit_Fxp #(
                        .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(M*Lookahead), .lut_size(`MAX_LUT_SIZE), .fact( hb_slice.Hb ), .n_int(n_int), .n_mant(n_mant)) Lookahead_LUT (
                        .sel(sampleahead[i*M*DSR +: M*Lookahead]), .clk(clkDS), .result(lookaheadResult)
                    );

            // Calculate lookback
            LUT_Unit_Fxp #(
                        .lut_comb(1), .adders_comb(`COMB_ADDERS), .size(M*Lookback), .lut_size(`MAX_LUT_SIZE), .fact( hf_slice.Hf ), .n_int(n_int), .n_mant(n_mant)) Lookback_LUT (
                        .sel(sampleback[(Stagger-1-i)*M*DSR +: M*Lookback]), .clk(clkDS), .result(lookbackResult)
                    );

            // Calculate final result
            logic signed[n_tot:0] tempResult;
            FxpPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) FinalAdder (.A(lookaheadResult), .B(lookbackResult), .clk(clkDS), .result(tempResult)); 

            always @(posedge clkDS) begin
                totResult[i] <= tempResult;
            end    
        end

        
    endgenerate
    
    // Shift out results
    logic signed[n_tot:0] finResult;
    logic signed[n_tot:0] resultShift[Stagger-1:0];
    generate
    if (Stagger > 1) begin
        logic clkDS_edge;
        always @(posedge clkDS) begin
            if(!rst)
                clkDS_edge <= 0;
            else
                clkDS_edge <= !clkDS_edge;
        end

        logic prevEdge;
        always @(posedge clkOut) begin
            prevEdge <= clkDS_edge;
        end

        for (genvar j = 0; j < Stagger ; j++ ) begin
            always @(posedge clkOut) begin
                if (clkDS_edge ^ prevEdge)
                    resultShift[j] <= totResult[j];
                else begin
                    if(j == (Stagger-1))
                        resultShift[j] <= 0;
                    else
                        resultShift[j] <= resultShift[j+1];
                end
            end
        end

        assign finResult = resultShift[0];
    end else begin
        assign finResult = totResult[0];
    end
    endgenerate

    // Format the result
    logic [`OUT_WIDTH-1:0] rectifiedResult;
    logic signed[`OUT_WIDTH-1:0] scaledResult;
    Fxp_To_Fxp #(.n_int_in(n_int), .n_mant_in(n_mant), .n_int_out(0), .n_mant_out(`OUT_WIDTH-1)) FinalScaler (.in( finResult ), .out( scaledResult ) );

    assign rectifiedResult[`OUT_WIDTH-1] = !scaledResult[`OUT_WIDTH-1];
    assign rectifiedResult[`OUT_WIDTH-2:0] = scaledResult[`OUT_WIDTH-2:0];

    // Final final result
    always @(posedge clkOut) begin
        out <= rectifiedResult;
    end
endmodule

`endif
