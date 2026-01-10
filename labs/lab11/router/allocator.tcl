analyze -sv09 allocator_pkg.sv
analyze -sv09 allocator.v
analyze -sv09 agent.v 
elaborate -top top -bbox_mod 1024
clock clk
reset rst

# Proof without abstraction
assert -name <embedded>::a3 {token_allocator_i.tokens_available <= TOKENS_NUMBER} 
prove -prop a3 -engine {M Hp}

for {set i 0} {$i < 4} {incr i} {
    stopat "agent\[$i\].agent_i.compute_needed_tokens";
    assume "agent\[$i\].agent_i.compute_needed_tokens > 'b0";
    assume "agent\[$i\].agent_i.compute_needed_tokens < TOKENS_NUMBER"
}
# Proof with abstraction
prove -prop a3 -engine {M Hp}
