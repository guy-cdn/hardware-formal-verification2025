analyze -sv09 counter.v
elaborate
clock clk
reset rst

# Abstraction using stopat; gives spurious CEX
stopat counter
prove -property test.ast
