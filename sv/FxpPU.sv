`ifndef FXPPU_SV_
`define FXPPU_SV_

`include "Util.sv"

// An adder or multiplier with 2 inputs
module FxpPU #(
    parameter   FPU_p::opcode op = FPU_p::ADD,
    parameter   n_int = 8,
                n_mant = 23
    ) (
    A, B, clk, result
);
    localparam n_tot = n_int + n_mant;
    input logic signed[n_tot:0] A, B;
    input logic clk;
    output logic signed[n_tot:0] result;

    generate
        case (op)
        FPU_p::ADD:
        begin
            assign result = A + B;
        end
        FPU_p::MULT:
        begin 
            logic signed[2*n_tot:0] AB;
            assign AB = A * B;
            assign result = AB >>> n_mant;
        end
        endcase
    endgenerate

endmodule

// An adder where number of inputs is decided by the size parameter
// Generates adders so it has the shortest delay possible
module Sum_Fxp #(
    parameter   size = 2,
                n_int = 8,
                n_mant = 23,
                adders_comb = 10
) (
    input logic signed[n_int+n_mant:0] in[size],
    input logic clk,
    output logic signed[n_int+n_mant:0] out
);
    localparam n_tot = n_int+n_mant;
    localparam AdderLayers = $clog2(size);
    logic signed[n_tot:0] adderResults[GetFirstReg(AdderLayers):0];
    
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
                logic signed[n_tot:0] tempResult;
                if ( i == 0 ) begin : Core_Gen
                    // Generate first layer
                    if ( ii < addNum ) begin : ADD_Gen
                        FxpPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) adder_ (.A(in[2*ii]), .B(in[2*ii + 1]), .clk(clk), .result(tempResult));
                    end else begin : Reg_Gen
                        assign tempResult = in[2*ii];
                    end
                end else begin : Layer_Gen
                    // Generate the rest of the layers
                    if ( ii < addNum) begin : ADD_Gen
                        FxpPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) adder_ (.A(adderResults[firstReg + 2*ii]), .B(adderResults[firstReg + 2*ii + 1]), .clk(clk), .result(tempResult));
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