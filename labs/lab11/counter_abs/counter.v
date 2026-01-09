module test(clk, rst, done, counter);

input clk;
input rst;
output done;
output reg[31:0] counter;
reg ok;

always @(posedge clk) begin
   if(rst) begin
      counter <= 32'h0;
      ok <= 1'b0;
   end else begin
      counter <= counter + 1;
      if (counter == 32'hFFFF) begin
          ok <= 1'b1;
      end
   end
end

assign done = (counter == 32'hFFFFFFFF);

ast: assert property (@(posedge clk) done |-> ok);

endmodule
