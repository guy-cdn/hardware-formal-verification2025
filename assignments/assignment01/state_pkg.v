package state_pkg;

typedef enum reg [1:0] {
    GREEN  = 2'b00,
    YELLOW = 2'b01,
    RED    = 2'b10
} state_t; 
    
endpackage : state_pkg
