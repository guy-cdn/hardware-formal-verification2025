
module fifo #(
  parameter int unsigned DEPTH = 8,   // number of entries
  parameter int unsigned WIDTH = 64   // data width
) (
  input  logic                 clk,
  input  logic                 rst,

  // Enqueue side (producer -> FIFO)
  input  logic                 enq_valid,
  output logic                 enq_ready,
  input  logic [WIDTH-1:0]     enq_data,

  // Dequeue side (FIFO -> consumer)
  output logic                 deq_valid,
  input  logic                 deq_ready,
  output logic [WIDTH-1:0]     deq_data,

  // Status
  output logic                 full,
  output logic                 empty
);

  // ------------------------------
  // Storage and pointers
  // ------------------------------
  localparam int unsigned PTRW = (DEPTH <= 1) ? 1 : $clog2(DEPTH);

  logic [WIDTH-1:0] mem [0:DEPTH-1];
  logic [PTRW-1:0]  wr_ptr, rd_ptr;
  logic [PTRW:0]    count;               // range 0..DEPTH

  // Handshake qualifies
  logic do_enq, do_deq;

  // ------------------------------
  // Flags & handshake
  // ------------------------------
  assign empty     = (count == 0);
  assign full      = (count == DEPTH);
  assign enq_ready = !full;
  assign deq_valid = !empty;

  assign do_enq = enq_valid && enq_ready;
  assign do_deq = deq_valid && deq_ready;

  // ------------------------------
  // Sequential logic
  // ------------------------------
  always_ff @(posedge clk or negedge rst) begin
    if (!rst) begin
      wr_ptr   <= '0;
      rd_ptr   <= '0;
      count    <= '0;
      deq_data <= '0;
    end else begin
      // write on enqueue
      if (do_enq) begin
        mem[wr_ptr] <= enq_data;
        wr_ptr      <= (wr_ptr == DEPTH-1) ? '0 : wr_ptr + 1'b1;
      end

      // read on dequeue (registered output)
      if (do_deq) begin
        deq_data <= mem[rd_ptr];
        rd_ptr   <= (rd_ptr == DEPTH-1) ? '0 : rd_ptr + 1'b1;
      end

      // count update
      unique case ({do_enq, do_deq})
        2'b10: count <= count + 1'b1;   // enqueue only
        2'b01: count <= count - 1'b1;   // dequeue only
        default: /* no change */ ;
      endcase
    end
  end

  logic [WIDTH-1:0] value;
  stable_value: assume property (@(posedge clk) 1 ##1 $stable(value));
  weak_consistency: assert property (
    do_enq && enq_data == value |-> do_deq[*DEPTH] implies ##[1:DEPTH] $past(do_deq) && deq_data == value);

  full_empty: cover property (@(posedge clk) !full ##[1:$] full ##[1:$] empty);
  count_range: assert property (@(posedge clk) count <= DEPTH);

endmodule
