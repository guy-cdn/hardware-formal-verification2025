analyze -sv09 toy.v
elaborate
reset ~rst
clock clk

# Lab demo
assert -name onehot0 {@(posedge clk) $onehot0(state)}
