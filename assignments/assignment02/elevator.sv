import elevator_pkg::*;

module elevator #(parameter FLOORS = 5)
(
    input logic clk,
    input logic rst,
    input logic [FLOORS-1:0] requestFloor,
    input logic [FLOORS-1:0] currentFloor,
    output logic [FLOORS-1:0] floorLight,
    output Direction direction,
    output DoorsOp doorsOp,
    output EngineOp engineOp
);

   logic [2:0] doorTimer;
   logic [FLOORS-1:0] nextFloor;

   always_comb
     if (engineOp == STOP)
       nextFloor = currentFloor;
     else if (direction == UP)
       nextFloor = currentFloor << 1;
     else nextFloor = currentFloor >> 1;   
   
    always_ff @(posedge clk)
      begin
         if (rst)
           begin
              doorsOp <= OPEN;
              doorTimer <= 3'h5;
           end
         else
           begin
              if (|(currentFloor & floorLight) && (doorsOp == CLOSE))
                begin
                   doorsOp <= OPEN;
                   doorTimer <= 3'h5;
                end
              else
                begin
                   if (doorsOp == OPEN)
                     begin
                        if (doorTimer > 3'h0)
                          doorTimer <= doorTimer - 3'h1;
                        else if (|floorLight)
                          doorsOp <= CLOSE;
                     end
                end
           end // else: !if(rst)
      end // always_ff @ (posedge clk)
            
   always_ff @(posedge clk)
     if (rst)
       engineOp <= STOP;
     else
       begin
          if (|((currentFloor | nextFloor) & floorLight) && (doorsOp == CLOSE))
            engineOp <= STOP;
          else if (!|(currentFloor & floorLight) && (doorsOp == CLOSE) && |floorLight)
            engineOp <= GO;
       end
   
    always_ff @(posedge clk)
      if (rst) floorLight <= 'b0;
      else floorLight <= (floorLight | requestFloor) & (~(currentFloor & {FLOORS{doorsOp == OPEN}}));
 
   reg higherReq;
   always_comb
     begin
        higherReq = 1'b0;
        for (int i = 0; i < FLOORS; i++)
          if (nextFloor[i])
            higherReq = 1'b0;
          else if (floorLight[i])
            higherReq = 1'b1;
     end

   reg lowerReq;
   always_comb
     begin
        lowerReq = 1'b0;
        for (int i = FLOORS - 1; i >= 0; i--)
          if (nextFloor[i])
            lowerReq = 1'b0;
          else if (floorLight[i])
            lowerReq = 1'b1;
     end
   

   always @(posedge clk)
     if (rst) direction <= UP;
     else
       begin
          if (direction == UP) begin
              if (lowerReq && !higherReq)
                  direction <= DOWN;
          end else begin
              if (!lowerReq && higherReq)
                  direction <= UP;
          end
       end
                                            
endmodule
