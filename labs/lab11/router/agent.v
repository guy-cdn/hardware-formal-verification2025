import allocator_pkg::*;

module agent #(TOKENS_NUMBER=8) (
    input       clk,
    input       rst,
    input       gnt,
    input       start,
    input [2:0] p1,
    input [2:0] p2,
    input [2:0] p3,
    output      req,
    output      ret);

    reg [$clog2(TOKENS_NUMBER):0] tokens_needed;
    reg [$clog2(TOKENS_NUMBER):0] tokens_aquired;   
    reg [2:0]                     processing_time;
    fsm_t state;

    reg [63:0] compute_needed_tokens;
   
    always begin
        compute_needed_tokens = 64'h123456789abcdef0;
        for (int ik = 0; ik < 81; ik++)
            compute_needed_tokens = (((p1 + p2 + compute_needed_tokens) ^ p3));
        compute_needed_tokens = (compute_needed_tokens % (TOKENS_NUMBER - 1'b1)) + 1'b1;
     end

    reg [2:0] compute_needed_cycles;
    always compute_needed_cycles = (((p1 ^ p2) + p3) % 3'h7) + 1'b1;

    always @(posedge clk)
        if (rst) state <= IDLE;
        else if ((state == IDLE) && start) state <= AQUIRE;
        else if ((state == AQUIRE) && (tokens_needed == (tokens_aquired + gnt))) state <= PROCESS;
        else if ((state == PROCESS) && (processing_time == 'b0)) state <= RETURN;
        else if ((state == RETURN) && (tokens_aquired == 'b1)) state <= IDLE;

    always @(posedge clk)
        if (rst || state == IDLE) tokens_aquired <= 'b0;
        else if ( gnt) tokens_aquired <= tokens_aquired + 1'b1;
        else if (state == RETURN && tokens_aquired > 0) tokens_aquired <= tokens_aquired - 1'b1;

    always @(posedge clk)
        if (rst) tokens_needed <= 'b0;
        else if ((state == IDLE) && start) tokens_needed <= compute_needed_tokens;

    always @(posedge clk)
        if (rst) processing_time <= 'b0;
        else if ((state == IDLE) && start) processing_time <= compute_needed_cycles;
        else if (state == PROCESS) processing_time <= processing_time - 1'b1;

    assign req = (state == AQUIRE);
    assign ret = (state == RETURN);
endmodule // agent

module top #(AGENTS_NUMBER=4, TOKENS_NUMBER=8) (
    input clk,
    input rst,
    input start [AGENTS_NUMBER],
    input [2:0] p1 [AGENTS_NUMBER],
    input [2:0] p2 [AGENTS_NUMBER],
    input [2:0] p3 [AGENTS_NUMBER]);

    reg [AGENTS_NUMBER-1:0] req;
    reg [AGENTS_NUMBER-1:0] gnt;
    reg [AGENTS_NUMBER-1:0] ret;
    logic [$clog2(TOKENS_NUMBER+1)-1:0] tokens_available_o;
   
    token_allocator #(.TOKENS_NUMBER(TOKENS_NUMBER), .AGENTS_NUMBER(AGENTS_NUMBER)) token_allocator_i(.*);
    genvar i;
    for (i = 0; i < AGENTS_NUMBER; i++)
        begin:agent
        agent #(.TOKENS_NUMBER(TOKENS_NUMBER)) agent_i(.gnt(gnt[i]), .req(req[i]), .ret(ret[i]), .p1(p1[i]), .p2(p2[i]), .p3(p3[i]), .start(start[i]), .*);
    end:agent

endmodule // top
