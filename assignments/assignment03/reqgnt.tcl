# Use this Tcl script to check your implementation in reqgnt.sv.
# Also, note the 'reset' definition, and use it accordingly, if needed, to reset your auxiliary code.
analyze -sv09 reqgnt.sv
elaborate
reset rst
clock clk
