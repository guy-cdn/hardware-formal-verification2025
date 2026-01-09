analyze -sv09 counter.v
elaborate
clock clk
reset rst

# Hard to converge
prove -property test.ast
