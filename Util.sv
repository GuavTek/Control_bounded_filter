// Misc utilities used in several modules

typedef struct packed {
    logic[15:0] r;
    logic[31:16] i;
} complex;

const logic[1:0] ALU_ADD = 2'b00;
const logic[1:0] ALU_SUB = 2'b01;
const logic[1:0] ALU_MULT = 2'b10;
