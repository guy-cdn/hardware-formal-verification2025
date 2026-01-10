
// -----------------------------------------------------------------------------
// token_allocator.sv
//   Parameterized token allocator with round-robin fairness.
//
// Protocol:
//   - Request/Grant: agent holds req[i] high until gnt[i] pulses (one token).
//   - Return: agent asserts ret[i]; every cycle ret[i] is high, one token is
//     immediately taken back (no ack). If the agent has no tokens, ret[i] is
//     ignored (no underflow).
//
// Fairness:
//   - Round-robin service of requests among agents while tokens are available.
//
// Throughput per cycle:
//   - Returns: many (one per agent that asserts ret[i], subject to held > 0).
//   - Grants: one (to the next eligible requester in RR order), after returns.
// -----------------------------------------------------------------------------

`timescale 1ns/1ps

module token_allocator #(
  parameter int unsigned TOKENS_NUMBER = 8,
  parameter int unsigned AGENTS_NUMBER = 4) (
  input  logic                           clk,
  input  logic                           rst,

  // Request (level) / Grant (pulse)
  input  logic [AGENTS_NUMBER-1:0]       req,
  output logic [AGENTS_NUMBER-1:0]       gnt,

  // Return (level): one token per cycle when high (no ack)
  input  logic [AGENTS_NUMBER-1:0]       ret,

  // Observability
  output logic [$clog2(TOKENS_NUMBER+1)-1:0] tokens_available_o);

  // ----------------------------------------------
  // Widths and storage
  // ----------------------------------------------
  localparam int TOKEN_W =  $clog2(TOKENS_NUMBER+1);
  localparam int AGENT_W =  $clog2(AGENTS_NUMBER);

  // Per-agent token counters (how many tokens each agent currently holds)

  // Total available tokens in the pool
  logic [TOKEN_W-1:0] tokens_available;

  // Round-robin pointer (for grants)
  int unsigned rr_req_ptr;

  // ----------------------------------------------
  // Helper: round-robin scan
  // Returns -1 if no bit is set in vec.
  // ----------------------------------------------
  function automatic int find_next_one (
    input logic [AGENTS_NUMBER-1:0] vec,
    input int unsigned start
  );
    for (int unsigned k = 0; k < AGENTS_NUMBER; k++) begin
      int unsigned idx = (start + k) % AGENTS_NUMBER;
      if (vec[idx]) return idx;
    end
    return -1;
  endfunction

  // ----------------------------------------------
  // Sequencing: returns first (increase availability), then grant
  // ----------------------------------------------
  // Availability after taking all returns
  logic [TOKEN_W:0] avail_after_returns;
  logic [TOKEN_W:0] returns_cnt; // extra bit for safe sum
  int              gnt_idx;
  always begin
      returns_cnt  = '0;
      for (int i = 0; i < AGENTS_NUMBER; i++) begin
          if (ret[i])  begin
              returns_cnt     = returns_cnt + 1'b1;
          end
      end
  end

  always gnt_idx = find_next_one(req, rr_req_ptr);
   
  always_ff @(posedge clk) begin
      if (rst) begin
          tokens_available <= TOKENS_NUMBER;
          rr_req_ptr       <= 0;
      end else begin

          // -----------------------------
          // Returns: accept one per agent per cycle if held > 0
          // -----------------------------

          avail_after_returns = tokens_available + returns_cnt;

          // -----------------------------
          // Grant: one per cycle, RR among req, only if availability > 0
          // -----------------------------

          if ((tokens_available + returns_cnt > 0) && gnt_idx != -1) begin
              rr_req_ptr            <= gnt_idx;
              avail_after_returns   = avail_after_returns - 1'b1;  // consume availability
          end

          // Commit availability
          tokens_available <= tokens_available + returns_cnt - |gnt;
      end
  end // always_ff @ (posedge clk)
   
  always begin
      gnt = 'b0;
      if ((tokens_available + returns_cnt > 0) && gnt_idx != -1)
          gnt[gnt_idx]          = 1'b1;                 // one-cycle pulse
  end
   
  assign tokens_available_o = tokens_available;

  // ----------------------------------------------
  // Optional Assertions (SVA) for correctness
  // Enable with +define+ASSERT_ON
  // ----------------------------------------------

endmodule
