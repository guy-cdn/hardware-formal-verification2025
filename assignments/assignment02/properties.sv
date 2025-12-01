import elevator_pkg::*;

module properties #(parameter FLOORS = 5)
(
    input logic              clk,
    input logic              rst,
    input logic [FLOORS-1:0] requestFloor,
    input logic [FLOORS-1:0] currentFloor,
    input logic [FLOORS-1:0] floorLight,
    input                    Direction direction,
    input                    DoorsOp doorsOp,
    input                    EngineOp engineOp
);

// ASSUME 1: Assume elevator moves up if engineOp is UP.
property prop_1;
    @(posedge clk) (engineOp == GO) && (direction == UP) |=> (currentFloor == $past(currentFloor << 1));
endproperty
assume_1: assume property (prop_1);

// ASSUME 2: Assume elevator moves down if engineOp is DOWN.
property prop_2;
    @(posedge clk) (engineOp == GO) && (direction == DOWN) |=> (currentFloor == $past(currentFloor >> 1));
endproperty
assume_2: assume property (prop_2);

// QUESTION 1(a): Assume elevator doesn't move if engineOp is STOP.
property prop_Q1a;
    @(posedge clk) 1; // EDIT THIS LINE
endproperty
assume_Q1a: assume property (prop_Q1a);

// QUESTION 1(b): Assume we start from some (specific, single) floor.
// NOTE: You are required to use auxiliary code for this question.
property prop_Q1b;
    @(posedge clk) 1; // EDIT THIS LINE
endproperty
assume_Q1b: assume property (prop_Q1b);

// QUESTION 2: Check we don't hit the basement.
property prop_Q2;
    @(posedge clk) 1; // EDIT THIS LINE
endproperty
assert_Q2: assert property (prop_Q2);

// QUESTION 3: Check we don't hit the roof.
property prop_Q3;
    @(posedge clk) 1; // EDIT THIS LINE
endproperty
assert_Q3: assert property (prop_Q3);

// QUESTION 4: Check door safety.
property prop_Q4;
    @(posedge clk) 1; // EDIT THIS LINE
endproperty
assert_Q4: assert property (prop_Q4);

// QUESTION 5:
property prop_Q5;
    @(posedge clk) 1; // EDIT THIS LINE
endproperty
assert_Q5: assert property (prop_Q5);

// QUESTION 6:
property prop_Q6;
    @(posedge clk) 1; // EDIT THIS LINE
endproperty
cover_Q6: cover property (prop_Q6);

// QUESTION 7:
property prop_Q7;
    @(posedge clk) 1; // EDIT THIS LINE
endproperty
cover_Q7: cover property (prop_Q7);

// QUESTION 8:
property prop_Q8;
    @(posedge clk) 1; // EDIT THIS LINE
endproperty
cover_Q8: cover property (prop_Q8);

// QUESTION 9:
property prop_Q9;
    @(posedge clk) 1; // EDIT THIS LINE
endproperty
cover_Q9: cover property (prop_Q9);

endmodule

bind elevator properties #(.FLOORS(FLOORS)) properties_i(.*);
