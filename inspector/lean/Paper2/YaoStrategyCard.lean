import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Counting complete response strategies

Statement source: Paper 2, locked `2026-09-22-protocol-labels-v12`,
`sections/07-yao.tex`, `yao:strategy-count` and the strategy enumeration
in the proof of `yao:capacity`.

A strategy with `t + 1` remaining turns consists of the next outgoing bit
and two continuation strategies, one for each possible incoming reply.
Both continuations are recorded, including replies that an actual input
never produces. This module proves the finite combinatorial count only;
the connection to actual alternating protocols belongs to `YaoStrategies`.
-/

namespace Paper2.Yao

/-- All binary response rules for `t` outgoing turns. The two continuations
at each node correspond to the next incoming bit being false or true. -/
def ResponseStrategy : ℕ → Type
  | 0 => PUnit
  | t + 1 => Bool × ResponseStrategy t × ResponseStrategy t

instance responseStrategyFintype : (t : ℕ) → Fintype (ResponseStrategy t)
  | 0 => inferInstanceAs (Fintype PUnit)
  | t + 1 => by
      letI := responseStrategyFintype t
      exact inferInstanceAs (Fintype (Bool × ResponseStrategy t × ResponseStrategy t))

instance responseStrategyDecidableEq : (t : ℕ) → DecidableEq (ResponseStrategy t)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | t + 1 => by
      letI := responseStrategyDecidableEq t
      exact inferInstanceAs (DecidableEq (Bool × ResponseStrategy t × ResponseStrategy t))

/-- The next outgoing bit and both incoming-bit continuations are independent
choices in the full response table. -/
theorem responseStrategy_card_succ (t : ℕ) :
    Fintype.card (ResponseStrategy (t + 1)) =
      2 * (Fintype.card (ResponseStrategy t) * Fintype.card (ResponseStrategy t)) := by
  change Fintype.card (Bool × ResponseStrategy t × ResponseStrategy t) = _
  simp

/-- Exact number of full response tables, including all hypothetical reply
histories. There is one empty strategy when `t = 0`. -/
theorem responseStrategy_card (t : ℕ) :
    Fintype.card (ResponseStrategy t) = 2 ^ (2 ^ t - 1) := by
  induction t with
  | zero => simp [ResponseStrategy]
  | succ t ih =>
      rw [responseStrategy_card_succ, ih]
      have hp : 0 < 2 ^ t := pow_pos (by decide) t
      have he : 1 + (2 ^ t - 1) + (2 ^ t - 1) = 2 ^ (t + 1) - 1 := by
        rw [pow_succ]
        omega
      calc
        2 * (2 ^ (2 ^ t - 1) * 2 ^ (2 ^ t - 1)) =
            2 ^ (1 + (2 ^ t - 1) + (2 ^ t - 1)) := by
              simp only [pow_add, pow_one]
              ring
        _ = 2 ^ (2 ^ (t + 1) - 1) := by rw [he]

/-- The empty history contributes no response bits. -/
theorem responseStrategy_card_zero : Fintype.card (ResponseStrategy 0) = 1 := by
  rw [responseStrategy_card]
  norm_num

/-- Two turns give the first bit and one second bit for either incoming
reply, as in the manuscript's eight-strategy example. -/
theorem responseStrategy_card_two : Fintype.card (ResponseStrategy 2) = 8 := by
  rw [responseStrategy_card]
  norm_num

end Paper2.Yao
