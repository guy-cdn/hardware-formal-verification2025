clear -all
analyze -sv09 {coop.sv}
elaborate -bbox_mul 1024 -top wrap
clock clk
reset rst

# BEGIN 
# Put the abstractions for the proof of <embedded>::wrap.valid_id before the next END
#
# END

check_return {prove -property {<embedded>::wrap.valid_id} -time_limit 300s -engine N -orch off} proven
