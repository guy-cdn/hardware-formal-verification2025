typedef enum reg [1:0] {SET, ADD, SUB, MUL} op_t;
typedef struct packed {
   reg [12:0] id;
   reg [5:0] length;
   reg [46:0] nothing;
} header_t;

typedef struct packed {
   op_t op;
   reg [63:0] data;
} arg_t;

typedef struct {
   reg is_header;
   union packed {
      header_t header;
      arg_t arg;
   }_m;
} message_t;

module generator
  (
   input        clk,
   input        rst,
   input [63:0] data_in,
   input [5:0]  len_in,
   input        op_t op,
   output       message_t msg
);
 
   reg [5:0] cnt;
   reg [5:0] len;
   reg [12:0] id_cnt;
   always @(posedge clk)
     if (rst) id_cnt <= 'b0;
     else if (cnt == len) id_cnt <= (id_cnt == 13'h1f82) ? id_cnt + 2'h2 : id_cnt + 1'b1;
   
   always @(posedge clk)
     if (rst) cnt <= 'b0;
     else cnt <= (cnt < len) ? cnt + 1'b1 : 'b0;

   always @(posedge clk)
     if (rst) len <= 'b0;
     else if (cnt == len) len <= len_in | 'b1;

   always_comb begin
      if (cnt == len)
        begin
           msg.is_header = 1'b1;
           msg._m.header.id = id_cnt;
           msg._m.header.length = (cnt == len) ? len_in : len;
        end
      else
        begin
           msg.is_header = 1'b0;
           msg._m.arg.op = (cnt == 1) ? SET : op;
           msg._m.arg.data = data_in;
        end // else: !if(cnt == len)
   end // always
endmodule // generator

module calculator
  (
   input             clk,
   input             rst,
   input             message_t msg,
   output reg [63:0] res,
   output reg [12:0] id,
   output reg        valid);

   reg [5:0] cnt;
   reg [5:0] len;

   always @(posedge clk)
     if (rst) cnt <= 'b0;
     else if (msg.is_header)
       cnt <= msg._m.header.length;
     else cnt <= cnt - 1'b1;

   always @(posedge clk)
     if (rst) id <= 'b0;
     else if (msg.is_header)
       id <= msg._m.header.id;

   always @(posedge clk)
     if (rst) len <= 'b0;
     else if (msg.is_header)
       len <= msg._m.header.length;

   always valid = (cnt == 'b0);

   always @(posedge clk)
     if (rst) res <= 'b0;
     else
       begin
          if (!msg.is_header)
            begin
               case (msg._m.arg.op)
                 SET: res <= msg._m.arg.data;
                 ADD: res <= res +  msg._m.arg.data;
                 SUB: res <= res -  msg._m.arg.data;
                 MUL: res <= res *  msg._m.arg.data;
               endcase // case (msg._m.arg.op)
            end
       end // else: !if(rst)

   a_set: assert property (@(posedge clk) !msg.is_header && (msg._m.arg.op == SET) |=> res == $past(msg._m.arg.data));
   a_add: assert property (@(posedge clk) !msg.is_header && (msg._m.arg.op == ADD) |=> res == $past(res + msg._m.arg.data));
   a_sub: assert property (@(posedge clk) !msg.is_header && (msg._m.arg.op == SUB) |=> res == $past(res - msg._m.arg.data));
   a_mul: assert property (@(posedge clk) !msg.is_header && (msg._m.arg.op == MUL) |=> res == $past(res *msg._m.arg.data));
endmodule // calculator

module wrap
  (
   input             clk,
   input             rst,
   input [63:0]      data_in,
   input [5:0]       len_in,
   input             op_t op,

   output reg [63:0] res,
   output reg [12:0] id,
   output            valid);

   message_t msg;
   generator generator_i(.*);
   calculator calculator_i(.*);
   
   reg [12:0] free_id;
   asm_stable_id: assume property (@(posedge clk) $stable(free_id));
   valid_id: assert property (@(posedge clk) msg.is_header && msg._m.header.id == free_id && msg._m.header.length > 'b0 |-> s_eventually valid && id == free_id);
   asm: assume property (@(posedge clk) 1 ##5 data_in == $past(data_in)*$past(data_in, 3)*$past(data_in, 5));
   id_cnt_skip: assert property (@(posedge clk) calculator_i.id == 13'h1f83|-> ##[456:497] valid);

endmodule // wrap
