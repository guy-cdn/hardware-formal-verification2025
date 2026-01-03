analyze -sv09 fifo.sv
elaborate -bbox_a 10000
reset ~rst_n
clock clk
prove -property fifo.ast -engine hps
prove -property fifo.ast -sst 20
#prove -property fifo.ast_strengthened -assert -engine hps
