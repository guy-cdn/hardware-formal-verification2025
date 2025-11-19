module toy(clk, rst, en, state);

input clk, rst, en;
output reg[2:0] state;

always @(posedge clk) begin
  if (~rst) begin
    state <= 3'b000;
  end else if (en) begin
    state[0] <= state == 3'b000;
    state[1] <= state[0];
    state[2] <= state[1];
  end
end

ast_weak:   assert property (@(posedge clk) en |->       (1 ##[0:$] !$onehot0(state)));
ast_strong: assert property (@(posedge clk) en |-> strong(1 ##[0:$] !$onehot0(state)));

endmodule
