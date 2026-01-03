module fifo #(
  parameter int DEPTH     = 32,
  parameter int DATA_W    = 8,
  localparam int ADDR_W   = $clog2(DEPTH)
) (
  input  logic                 clk,
  input  logic                 rst_n,
  input  logic                 wr_en,
  input  logic                 rd_en,
  input  logic [DATA_W-1:0]    din,
  output logic [DATA_W-1:0]    dout,
  output logic                 full,
  output logic                 empty
);

  // Storage and pointers
  logic [DATA_W-1:0] mem [DEPTH];
  logic [ADDR_W-1:0] wptr, rptr;

  // Count tracks occupancy in [0..DEPTH]
  logic [ADDR_W-1:0]   count;

  // Flags
  assign full  = (count == DEPTH);
  assign empty = (count == 0);

  // Write path
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      wptr <= '0;
    end else if (wr_en && !full) begin
      mem[wptr] <= din;
      wptr      <= wptr + 1'b1;
    end
  end

  // Read path
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      rptr <= '0;
      dout <= '0;
    end else if (rd_en && !empty) begin
      dout <= mem[rptr];
      rptr <= rptr + 1'b1;
    end
  end

  // Occupancy count update (net +1, 0, or -1 per cycle)
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      count <= '0;
    end else begin
      unique case ({(wr_en && !full), (rd_en && !empty)})
        2'b10: count <= count + 1'b1;  // write only
        2'b01: count <= count - 1'b1;  // read only
        default: /* 2'b00 or 2'b11 */ count <= count; // no op or simultaneous
      endcase
    end
  end

ast: assert property (@(posedge clk) wptr >= rptr |-> wptr - rptr == count);
ast_strengthened: assert property (@(posedge clk) 
  (wptr >= rptr |-> wptr - rptr == count) and
  (wptr <  rptr |-> DEPTH + wptr - rptr == count));

endmodule
