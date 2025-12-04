# Compile
analyze -sv09 fifo.sv

# Elaborate
elaborate

# Define reset and clock
reset ~rst
clock clk

# Prove the count range check.
# Use engine B, which is a single property bounded model checking engine.
# Use increased verbosity so as to see some extra information about the run.
# Disable proof orchestration, to make sure only engine B runs.
prove -property fifo.count_range -engine B -verbosity 11 -orchestration off
