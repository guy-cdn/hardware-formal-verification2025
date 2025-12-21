analyze -sv09 15puzzle.sv
elaborate
clock clk
reset ~rst

# This will prove the property you need to implement using BMC.  You need to
# make sure that the trace found by this proof has the desired length, as
# specified in the question. 
prove -property puzzle.A -orch off -engine B
