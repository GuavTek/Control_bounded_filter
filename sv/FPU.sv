`ifndef FPU_SV_
`define FPU_SV_

`include "Util.sv"

module FPU #(
    parameter   FPU_p::opcode op = FPU_p::ADD,
    parameter   n_exp = 8, n_mant = 23,
    parameter   type float_t = struct {logic sign; logic[7:0] exp; logic[22:0] mant;}
) (
    A, B, clk, result
);
    input float_t A, B;
    input logic clk;
    output float_t result;
    localparam n_tot = n_exp + n_mant;

    logic[n_tot + 1:0] s1, s2, r1;

    fNToRecFN #(.expWidth(n_exp), .sigWidth(n_mant+1)) aConv (.in(A), .out(s1));
    fNToRecFN #(.expWidth(n_exp), .sigWidth(n_mant+1)) bConv (.in(B), .out(s2));
    recFNToFN #(.expWidth(n_exp), .sigWidth(n_mant+1)) resConv (.in(r1), .out(result));

    generate
        case (op)
        FPU_p::ADD:
        begin
            logic[4:0] dummy;
            addRecFN #(.expWidth(n_exp), .sigWidth(n_mant+1)) add1 (.control(`flControl_tininessAfterRounding), .subOp(1'b0), .a(s1), .b(s2), .roundingMode(`round_near_even), .out(r1), .exceptionFlags(dummy));
        end
        FPU_p::MULT:
        begin 
            logic[4:0] dummy;
            mulRecFN #(.expWidth(n_exp), .sigWidth(n_mant+1)) mul1 (.control(`flControl_tininessAfterRounding), .a(s1), .b(s2), .roundingMode(`round_near_even), .out(r1), .exceptionFlags(dummy));
        end
        endcase
    endgenerate

endmodule

// An adder where number of inputs is decided by the size parameter
// Generates adders so it has the shortest delay possible
module Sum_Flp #(
    parameter   size = 2,
                f_exp = 8,
                f_mant = 23,
                adders_comb = 10,
    parameter   type float_t = struct {logic sign; logic[7:0] exp; logic[22:0] mant;}
) (
    input float_t in[size],
    input logic clk,
    output float_t out
);
    localparam AdderLayers = $clog2(size);
    float_t adderResults[GetFirstReg(AdderLayers):0];
    
    // Calculate number of adders in layer n
    function automatic int GetAdderNum(int n);
        int temp = size;
        for(int i = 0; i < n; i++) begin
            //temp = $ceil(temp/2);
            temp += 1;
            temp >>= 1;
        end
        //temp = $floor(temp/2);
        temp >>= 1;
        return temp;
    endfunction

    // Calculate number of result registers in layer n
    function automatic int GetRegsNum(int n);
        int temp = size;
        for (int i = 0; i <= n; i++) begin
            //temp = $ceil(temp/2);
            temp += 1;
            temp >>= 1;
        end
        return temp;
    endfunction

    // Calculate the index of a layers first register 
    function automatic int GetFirstReg(int n);
        int temp = 0;
        for (int i = 1; i < n; i++)
            temp += GetRegsNum(i-1);
        return temp;
    endfunction

    // Generate adders
    generate
        // Failsafe in case the number of adders is 0 or less
        if (AdderLayers <= 0) begin : No_Adders
            assign adderResults[0] = in[0];
        end
        
        // Generate the layers
        for (genvar i = 0; i < AdderLayers; i++ ) begin : ADDER_Gen
            localparam addNum = GetAdderNum(i);
            localparam regNum = GetRegsNum(i);
            localparam firstReg = GetFirstReg(i);
            localparam nextReg = GetFirstReg(i+1);

            `ifdef VERBOSE_LVL
                if(`VERBOSE_LVL > 2)
                    $info("layer: %3d, addNum: %4d, regNum: %4d, firstres: %4d, nextres: %4d", i, addNum, regNum, firstReg, nextReg);
            `endif

            // Generate the adders and registers within a layer
            for (genvar ii = 0; ii < regNum; ii++) begin : Layer_Instance_Gen
                float_t tempResult;
                if ( i == 0 ) begin : Core_Gen
                    // Generate first layer
                    if ( ii < addNum ) begin : ADD_Gen
                        FPU #(.op(FPU_p::ADD), .n_exp(f_exp), .n_mant(f_mant), .float_t(float_t)) adder_ (.A(in[2*ii]), .B(in[2*ii + 1]), .clk(clk), .result(tempResult));
                    end else begin : Reg_Gen
                        assign tempResult = in[2*ii];
                    end
                end else begin : Layer_Gen
                    // Generate the rest of the layers
                    if ( ii < addNum) begin : ADD_Gen
                        FPU #(.op(FPU_p::ADD), .n_exp(f_exp), .n_mant(f_mant), .float_t(float_t)) adder_ (.A(adderResults[firstReg + 2*ii]), .B(adderResults[firstReg + 2*ii + 1]), .clk(clk), .result(tempResult));
                    end else begin : Reg_Gen
                        assign tempResult = adderResults[firstReg + 2*ii];
                    end
                end

                // Break up long strings of combinatorial adders
                if (((i+1) % adders_comb) > 0) begin : Comb_Gen
                    assign    adderResults[nextReg + ii] = tempResult;
                end else begin : FF_Gen
                    always @(posedge clk) begin
                        adderResults[nextReg + ii] <= tempResult;
                    end
                end
                
            end
            
        end
    endgenerate

    assign out = adderResults[GetFirstReg(AdderLayers)];

endmodule

`endif