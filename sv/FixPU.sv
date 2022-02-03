`ifndef FIXPU_SV_
`define FIXPU_SV_

`include "Util.sv"

// An adder or multiplier with 2 inputs
module FixPU #(
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
module FixSum #(
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

    function automatic int GetRegsNum(int n);
        int temp = size;
        for (int i = 0; i <= n; i++) begin
            //temp = $ceil(temp/2);
            temp += 1;
            temp >>= 1;
        end
        return temp;
    endfunction

    function automatic int GetFirstReg(int n);
        int temp = 0;
        for (int i = 1; i < n; i++)
            temp += GetRegsNum(i-1);
        return temp;
    endfunction

    // Generate adders
    generate
        genvar layer, ii;
        if (AdderLayers == 0) begin : No_Adders
            assign adderResults[0] = in[0];
        end
        
        for (layer = AdderLayers; layer > 0 ; layer-- ) begin : ADDER_Gen
            localparam i = layer - 1;
            localparam addfloor = GetAdderNum(i);
            localparam addceil = GetRegsNum(i);
            localparam firstRes = GetFirstReg(i);
            localparam nextRes = GetFirstReg(i+1);

            `ifdef VERBOSE_LVL
                if(`VERBOSE_LVL > 2)
                    $info("layer: %3d, addfloor: %4d, addceil: %4d, firstres: %4d, nextres: %4d", i, addfloor, addceil, firstRes, nextRes);
            `endif

            for ( ii = 0; ii < addceil; ii++) begin : Layer_Instance_Gen
                logic signed[n_tot:0] tempResult;
                if ( i == 0 ) begin : Core_Gen
                    if ( ii < addfloor ) begin : ADD_Gen
                        FixPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) adder_ (.A(in[2*ii]), .B(in[2*ii + 1]), .clk(clk), .result(tempResult));
                    end else begin : Reg_Gen
                        assign tempResult = in[2*ii];
                    end
                end else begin : Layer_Gen
                    if ( ii < addfloor) begin : ADD_Gen
                        FixPU #(.op(FPU_p::ADD), .n_int(n_int), .n_mant(n_mant)) adder_ (.A(adderResults[firstRes + 2*ii]), .B(adderResults[firstRes + 2*ii + 1]), .clk(clk), .result(tempResult));
                    end else begin : Reg_Gen
                        assign tempResult = adderResults[firstRes + 2*ii];
                    end
                end

                if (((i+1) % adders_comb) > 0) begin : Comb_Gen
                    assign    adderResults[nextRes + ii] = tempResult;
                end else begin : FF_Gen
                    always @(posedge clk) begin
                        adderResults[nextRes + ii] <= tempResult;
                    end
                end
                
            end
            
        end
    endgenerate

    assign out = adderResults[GetFirstReg(AdderLayers)];

endmodule

`endif