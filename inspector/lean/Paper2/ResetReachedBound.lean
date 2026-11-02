import Paper2.CodeHeaderDraw
import Paper2.CodeInterpreterReset
import EthInapproximability.CurrentPaper.BitMachineStackGrowth
import Mathlib.Tactic

/-! A prospective reset-clock bound on a physically reached draw result.
No reset is run at this point: the header and ticket still carry operands. -/

namespace Paper2.ResetReachedBound

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.BitMachineStackGrowth
open Paper2.GeneratorCode Paper2.GeneratorSerialization

noncomputable section

abbrev Stack := CodeInterpreterReset.Stack

def drawClock (c : Code) (B R : Nat) : Nat :=
  CodeHeaderMachine.headerCost c + CodeHeaderDraw.stagingCost c +
    LoadedTicketMachine.loaderBound (CodeHeaderDraw.denominator c) B R +
    LoadedTicketMachine.ticketBound (CodeHeaderDraw.denominator c) B R + 1

/-- A constant determined by the one fixed header/draw program, not by the
code, public parameters, random tape, or residual log workspace. -/
def drawPushBound : Nat := perStep CodeHeaderDraw.program

def publicResetCap (c : Code) (B R : Nat) : Nat :=
  CodeInterpreterReset.clearCount * (drawPushBound * drawClock c B R) +
    CodeInterpreterReset.clearCount + 2

/-- Shortening each cell that reset would clear cannot increase its clock.
The five kept cells may change arbitrarily. -/
theorem clock_mono (S T : Stack → List Bool)
    (h : ∀ i : Fin CodeInterpreterReset.clearCount,
      (S (CodeInterpreterReset.slot i)).length ≤
        (T (CodeInterpreterReset.slot i)).length) :
    CodeInterpreterReset.clock S ≤ CodeInterpreterReset.clock T := by
  unfold CodeInterpreterReset.clock
  have hs : (∑ i : Fin CodeInterpreterReset.clearCount,
      (S (CodeInterpreterReset.slot i)).length) ≤
      ∑ i : Fin CodeInterpreterReset.clearCount,
        (T (CodeInterpreterReset.slot i)).length := by
    apply Finset.sum_le_sum
    intro i _
    exact h i
  omega

theorem safe_point_clock_le (S T : Stack → List Bool)
    (h : ∀ k : Stack, ¬ CodeInterpreterReset.keep k →
      (S k).length ≤ (T k).length) :
    CodeInterpreterReset.clock S ≤ CodeInterpreterReset.clock T := by
  apply clock_mono S T
  intro i
  exact h _ (CodeInterpreterReset.slot_not_keep i)

/-- The encoded-draw machine starts with no data at any reset-clear cell.
Only code, output, tape, and public B/R occupy the five kept cells. -/
theorem start_clear_empty (code outputWord tape : List Bool) (B R : Nat)
    (k : Stack) (hk : ¬ CodeInterpreterReset.keep k) :
    (CodeHeaderDraw.start code outputWord tape B R).stk k = [] := by
  change CodeHeaderDraw.startBank code outputWord tape B R k = []
  cases k with
  | inl j =>
      rw [CodeHeaderDraw.startBank,
        bank_outside CodeHeaderDraw.headerSlot
          (CodeHeaderDraw.foreignBank outputWord 0 B R tape)
          (CodeHeaderMachine.initial code).stk (.inl j)]
      · cases j with
        | inl x =>
            fin_cases x <;> simp_all [CodeHeaderDraw.foreignBank,
              DrawParameterLoader.initialBank, DrawParameterLoader.mainBank,
              CodeInterpreterReset.keep]
        | inr x =>
            simp [CodeHeaderDraw.foreignBank,
              DrawParameterLoader.initialBank, DrawParameterLoader.mainBank]
      · rintro ⟨x,hx⟩
        cases hx
  | inr j =>
      cases j with
      | inl x =>
          rw [CodeHeaderDraw.startBank,
            ← show CodeHeaderDraw.headerSlot x =
              (.inr (.inl x) : Stack) by rfl,
            bank_at]
          fin_cases x <;> simp_all [CodeHeaderMachine.initial,
            CodeHeaderMachine.cfg, CodeHeaderMachine.contents,
            CodeInterpreterReset.keep]
      | inr x =>
          exact False.elim (hk (by simp [CodeInterpreterReset.keep]))

theorem start_clear_slot_empty (code outputWord tape : List Bool) (B R : Nat)
    (i : Fin CodeInterpreterReset.clearCount) :
    (CodeHeaderDraw.start code outputWord tape B R).stk
      (CodeInterpreterReset.slot i) = [] :=
  start_clear_empty code outputWord tape B R _
    (CodeInterpreterReset.slot_not_keep i)

/-- The residual log bank is included: every cleared cell of a reached state
is bounded by physical per-transition growth from an initially empty cell. -/
theorem clock_bound_from_run (code outputWord tape : List Bool) (B R t : Nat)
    (C : CodeHeaderDraw.Config)
    (hr : CodeHeaderDraw.run t
      (CodeHeaderDraw.start code outputWord tape B R) = C) :
    CodeInterpreterReset.clock C.stk ≤
      CodeInterpreterReset.clearCount * (drawPushBound * t) +
        CodeInterpreterReset.clearCount + 2 := by
  have hslot (i : Fin CodeInterpreterReset.clearCount) :
      (C.stk (CodeInterpreterReset.slot i)).length ≤ drawPushBound * t := by
    have hg := run_growth CodeHeaderDraw.program
      (CodeHeaderDraw.start code outputWord tape B R) t
      (CodeInterpreterReset.slot i)
    change ((CodeHeaderDraw.run t
      (CodeHeaderDraw.start code outputWord tape B R)).stk
      (CodeInterpreterReset.slot i)).length ≤
      ((CodeHeaderDraw.start code outputWord tape B R).stk
        (CodeInterpreterReset.slot i)).length + drawPushBound * t at hg
    rw [hr, start_clear_slot_empty code outputWord tape B R i] at hg
    simpa using hg
  have hsum : (∑ i : Fin CodeInterpreterReset.clearCount,
      (C.stk (CodeInterpreterReset.slot i)).length) ≤
      CodeInterpreterReset.clearCount * (drawPushBound * t) := by
    calc
      _ ≤ ∑ _i : Fin CodeInterpreterReset.clearCount, drawPushBound * t := by
        apply Finset.sum_le_sum
        intro i _
        exact hslot i
      _ = _ := by simp [mul_comm]
  unfold CodeInterpreterReset.clock
  omega

/-- A reached draw-result bank has a reset clock bounded only by public/code
data and the fixed physical program. This is prospective: ticket and header
operands must be consumed before the reset is actually invoked. -/
theorem reached_result_clock (c : Code) (hc : CodeHeaderDraw.DrawHead c)
    (B R N : Nat) (hB : Nat.clog 2 (CodeHeaderDraw.denominator c) ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (rest outputWord : List Bool) :
    ∃ t : Nat, ∃ F : DrawParameterLoader.LogCopyStack → List Bool,
      t ≤ drawClock c B R ∧
      CodeHeaderDraw.run t
        (CodeHeaderDraw.start (encodeCode c ++ rest) outputWord
          (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        CodeHeaderDraw.resultCfg (CodeHeaderDraw.denominator c) B R N hB tape
          (CodeHeaderMachine.headerKind c)
          (CodeHeaderMachine.headerTail c rest)
          (CodeHeaderMachine.headerN c)
          (CodeHeaderMachine.headerA c)
          (CodeHeaderMachine.headerB c) outputWord F ∧
      CodeInterpreterReset.clock
        (CodeHeaderDraw.resultCfg (CodeHeaderDraw.denominator c) B R N hB tape
          (CodeHeaderMachine.headerKind c)
          (CodeHeaderMachine.headerTail c rest)
          (CodeHeaderMachine.headerN c)
          (CodeHeaderMachine.headerA c)
          (CodeHeaderMachine.headerB c) outputWord F).stk ≤
        publicResetCap c B R := by
  obtain ⟨t,F,ht,hr⟩ :=
    CodeHeaderDraw.encoded_draw_head c hc B R N hB tape rest outputWord
  refine ⟨t,F,?_,hr,?_⟩
  · simpa [drawClock] using ht
  · have hg := clock_bound_from_run (encodeCode c ++ rest) outputWord
      (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R t _ hr
    have hmul : drawPushBound * t ≤ drawPushBound * drawClock c B R :=
      Nat.mul_le_mul_left _ (by simpa [drawClock] using ht)
    have hmul2 := Nat.mul_le_mul_left CodeInterpreterReset.clearCount hmul
    unfold publicResetCap
    omega

#print axioms reached_result_clock
#print axioms safe_point_clock_le

end

end Paper2.ResetReachedBound
