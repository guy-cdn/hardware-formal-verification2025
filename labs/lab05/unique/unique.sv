module unique_prop(clk, rst, rvfi_valid, rvfi_order);

  input           clk;
  input           rst;
  input           rvfi_valid;
  input reg[63:0] rvfi_order;

  wire      en;           // When high for the first time, save rvfi_order
  reg       saved;        // Indicates whether order is saved in saved_order
  reg[63:0] saved_order;  // Saved rvfi_order

  always @(posedge clk) begin
      if (!rst) begin 
          saved <= 1'b0;
      end else begin
          if (rvfi_valid && !saved && en) begin
              saved_order <= rvfi_order;
              saved <= 1'b1;
          end
      end
  end

  uniq_ast: assert property (@(posedge clk) rvfi_valid && saved |-> rvfi_order != saved_order);

endmodule

// Bind the above module to the ibex_if_stage module.
bind ibex_top unique_prop prop_i(clk_i, rst_ni, rvfi_valid, rvfi_order);
