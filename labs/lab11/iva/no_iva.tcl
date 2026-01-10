analyze -sv09 fifo.sv
elaborate -bbox_a 100000
reset ~rst_n
clock clk
prove -property fifo.ast -engine M
