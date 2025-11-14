analyze -sv09 state_pkg.v
analyze -sv09 traffic_light.v
# Uncomment the line below (remove the "#") once you finished implementing properties.v
# analyze -sv09 properties.v
elaborate
clock clk
reset rst
