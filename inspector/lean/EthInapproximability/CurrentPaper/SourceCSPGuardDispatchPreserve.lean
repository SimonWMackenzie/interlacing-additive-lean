import EthInapproximability.CurrentPaper.SourceCSPGuardDispatchSequence

/-!
# Foreign-stack preservation for the raw CSP branch selector

The selector observes the vertex word, unary count, and unread suffix but
physically pops only its one-bit status cell.  This reusable invariant keeps
the successful operands available to the positive-cap and row-loop adapter.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPGuardDispatchPreserve

open Turing BitMachineEncoding

abbrev Stack := SourceCSPGuardDispatch.Stack

theorem step_preserves (c : SourceCSPGuardDispatch.Config) (k : Stack)
    (hk : k ≠ SourceCSPGuardDispatch.statusSlot) :
    (advance SourceCSPGuardDispatch.program c).stk k = c.stk k := by
  cases c with
  | mk l v S =>
      change k ≠ SourceCSPGuardStatus.statusSlot at hk
      cases l with
      | none => rfl
      | some l =>
          cases l with
          | status =>
              simp [advance, TM2.step, TM2.stepAux,
                SourceCSPGuardDispatch.program]
              cases h : ((S SourceCSPGuardDispatch.statusSlot).head? == some true) <;>
                simp [h, SourceCSPGuardDispatch.statusSlot, hk]
          | vertex =>
              simp [advance, TM2.step, TM2.stepAux,
                SourceCSPGuardDispatch.program]
              cases h : (S SourceCSPGuardDispatch.vertexSlot).head?.isSome <;>
                simp [h]
          | zeroCount =>
              simp [advance, TM2.step, TM2.stepAux,
                SourceCSPGuardDispatch.program]
              cases h : (S SourceCSPGuardDispatch.countSlot).head?.isSome <;>
                simp [h]
          | zeroEof =>
              simp [advance, TM2.step, TM2.stepAux,
                SourceCSPGuardDispatch.program]
              cases h : (S SourceCSPGuardDispatch.sourceSlot).head?.isSome <;>
                simp [h]
          | reject =>
              simp [advance, TM2.step, TM2.stepAux,
                SourceCSPGuardDispatch.program]
          | zero =>
              simp [advance, TM2.step, TM2.stepAux,
                SourceCSPGuardDispatch.program]
          | positive =>
              simp [advance, TM2.step, TM2.stepAux,
                SourceCSPGuardDispatch.program]

theorem run_preserves (t : Nat) (S : Stack → List Bool) (k : Stack)
    (hk : k ≠ SourceCSPGuardDispatch.statusSlot) :
    (SourceCSPGuardDispatch.run t S).stk k = S k := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [SourceCSPGuardDispatch.run,
        Function.iterate_succ_apply']
      exact (step_preserves _ k hk).trans ih

end EthInapproximability.CurrentPaper.SourceCSPGuardDispatchPreserve
