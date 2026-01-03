# Simple example of the base and induction step checks done by induction

analyze -sv09 counter.v
elaborate 
clock clk
reset rst

# Base (manual)
#
prove -property counter.ast -engine B -max_trace_length 1

# Induction step (manual)
#
#reset -none
#property -name induction_step {c1 == c2 |=> c1 == c2}
#prove -property induction_step -engine B -max_trace_length 2 -first_trace_attempt 2
