# Compile
analyze -sv09 fifo.sv 

# Elaborate
elaborate -top fifo -parameter DEPTH 128

# Define reset and clock
reset ~rst
clock clk

# Setup
set_engine_mode B
set_prove_orchestration off
set_prove_verbosity 11

# Prove the full-empty cover for 10 seconds and give up.
prove -property fifo.full_empty -time_limit 10s

# Break the proof (search for cover) to multiple parts.
cover -name c1 {count == 30}
cover -name c2 {count == 60}
cover -name c3 {count == 90}
cover -name c4 {count == 120}
cover -name c5 {full}
cover -name c6 {full ##1 (count == 120)[->1]}
cover -name c7 {full ##1 (count == 90)[->1]}
cover -name c8 {full ##1 (count == 60)[->1]}
cover -name c9 {full ##1 (count == 30)[->1]}

prove -property {c1 c2 c3 c4 c5 c6 c7 c8 c9 fifo.full_empty} -engine L
