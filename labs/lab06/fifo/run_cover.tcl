# Compile
analyze -sv09 fifo.sv

# Elaborate
elaborate

# Define reset and clock
reset ~rst
clock clk

# Prove the full-empty cover.
# Use engine B, which is a single property bounded model checking engine.
# Use increased verbosity so as to see some extra information about the run.
# Disable proof orchestration, to make sure only engine B runs.
prove -property fifo.full_empty -engine B -verbosity 11 -orchestration off
