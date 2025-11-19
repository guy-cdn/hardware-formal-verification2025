module toy(clk, rst, req, sig);

input clk, rst, req, sig;

ast: assert property (@(posedge clk) req |=> !req || $stable(sig));

endmodule
