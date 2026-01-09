analyze -sv09 counter.v
elaborate
clock clk
reset rst

# Using counter abstraction; property is proven
abstract -counter counter
prove -property test.ast
