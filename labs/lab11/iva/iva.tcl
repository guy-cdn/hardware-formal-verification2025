analyze -sv09 fifo.sv
elaborate -bbox_a 100000
reset ~rst_n
clock clk
abstract -init_value wptr
abstract -init_value rptr
abstract -init_value count
assume -bound 1 {wptr - rptr == count || DEPTH + wptr - rptr == count}
prove -property fifo.ast -engine M
