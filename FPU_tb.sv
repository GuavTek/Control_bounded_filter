`include "Util.sv"
`include "FPU.sv"

module moduleName #(
    parameter testLength = 10
) ();
    // Define clock
    logic clk;
    always #5 clk = ~clk;

    // Define signals
    floatType in_a, in_b, out_sum, out_prod;

    // Instantiate DUTs
    FPU #() DUT_ADD (.A(in_a), .B(in_b), .op(ADD), .result(out_sum));
    FPU #() DUT_MULT (.A(in_a), .B(in_b), .op(MULT), .result(out_prod));
    
    initial begin

        in_a = rtof(0.0);
        in_b = rtof(0.0);

        repeat(testLength) @(posedge clk) begin
            // Check results
            real numberA, numberB, resultSum, resultProd;
            numberA = ftor(in_a);
            numberB = ftor(in_b);
            resultSum = ftor(out_sum);
            resultProd = ftor(out_prod);

            assert(resultProd == numberA * numberB)
            else $display("Wrong product, %f and %f does not equal %f", numberA, numberB, resultProd);
            assert(resultSum == numberA + numberB)
            else $display("Wrong sum, %f and %f does not equal %f", numberA, numberB, resultSum);

            // Generate random numbers
            std::randomize(numberA) with {
                numberA > 0.00001 ; numberA < 9.9;
            };

            std::randomize(numberB) with {
                numberB > 0.00001 ; numberB < 9.9;
            };

            // Convert from real to float
            in_a = rtof(numberA);
            in_b = rtof(numberB);

            // Sanity check conversions
            real tempA, tempB;
            tempA = ftor(in_a);
            tempB = ftor(in_b);
            assert(tempA == numberA)
            else $display("Warning! %f was converted to %f", numberA, tempA);
            assert(tempB == numberB)
            else $display("Warning! %f was converted to %f", numberB, tempB);
        end
    end
    

endmodule