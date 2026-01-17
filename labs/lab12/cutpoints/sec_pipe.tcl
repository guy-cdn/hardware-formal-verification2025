clear -all
check_sec -analyze -spec -sv pipe.sv
check_sec -analyze -imp -sv pipe.sv
check_sec -elaborate -spec -top spec
check_sec -elaborate -imp -top imp
check_sec -setup
check_sec -auto_map_reset_x_values on

clock clk
reset rst
check_sec -gen

check_sec -prove -no_auto -time_limit 30

check_sec -map -spec mid -cut both

check_sec -prove -no_auto -time_limit 30
