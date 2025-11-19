module toy(clk, rst, A, B, C);

input clk, rst, A, B, C;

P8: cover property (@(posedge clk) A |-> B[->2] ##1 C);

endmodule
