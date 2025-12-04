# Compile
analyze -sv09 fifo.sv 

# Elaborate
elaborate -top fifo -parameter DEPTH 128 -bbox_a 100000

# Define reset and clock
reset ~rst
clock clk

# Prove the full-empty cover.
prove -property fifo.full_empty -engine B -verbosity 11 -orchestration off

# Prove the full-empty cover again, but start at Trace Attempt 257
clear -result
set_engineB_first_trace_attempt 257
prove -property fifo.full_empty -engine B -verbosity 11 -orchestration off
