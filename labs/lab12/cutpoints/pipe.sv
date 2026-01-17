module pipe1 
  (input clk,
   input rst,
   input [31:0] a,
   input [31:0] b,
   input [31:0] c,
   output [31:0] out
   );

   reg [31:0] f1;
   reg [31:0] f2;
   always @(posedge clk)
     if(rst) f1 <= 'b0;
     else f1 <= a + b;
   
   always @(posedge clk)
     if(rst) f2 <= 'b0;
     else f2 <= b + c;

   assign out = f2 + f1;
endmodule // pipe1

module pipe2 
  (input clk,
   input rst,
   input [31:0] a,
   input [31:0] b,
   input [31:0] c,
   output [31:0] out
   );

   reg [31:0] f1;
   reg [31:0] f2;
   always @(posedge clk)
     if(rst) f1 <= 'b0;
     else f1 <= a + c;
   
   always @(posedge clk)
     if(rst) f2 <= 'b0;
     else f2 <= b + b;

   assign out = f1 + f2;
endmodule // pipe1

module spec #(D=10)
  (
   input clk,
   input rst,
   input [31:0] a,
   input [31:0] b [D],
   input [31:0] c [D],
   output [31:0] out
   );

   reg [31:0] mid [D-1];
   pipe1 p1 (.clk(clk), .rst(rst), .a(a), .b(b[0]), .c(c[0]), .out(mid[0]));
   genvar i;
   for (i = 0; i < D-2; i++)
     begin:pp
        pipe1 p (.clk(clk), .rst(rst), .a(mid[i]), .b(b[i+1]), .c(c[i+1]), .out(mid[i+1]));
     end:pp
   pipe1 pd (.clk(clk), .rst(rst), .a(mid[D-2]), .b(b[D-1]), .c(c[D-1]), .out(out));
endmodule // spec

module imp #(D=10)
  (
   input clk,
   input rst,
   input [31:0] a,
   input [31:0] b [D],
   input [31:0] c [D],
   output [31:0] out
   );

   reg [31:0] mid [D-1];
   pipe2 p1 (.clk(clk), .rst(rst), .a(a), .b(b[0]), .c(c[0]), .out(mid[0]));
   genvar i;
   for (i = 0; i < D-2; i++)
     begin:pp
        pipe2 p (.clk(clk), .rst(rst), .a(mid[i]), .b(b[i+1]), .c(c[i+1]), .out(mid[i+1]));
     end:pp
   pipe2 pd (.clk(clk), .rst(rst), .a(mid[D-2]), .b(b[D-1]), .c(c[D-1]), .out(out));
endmodule // spec
