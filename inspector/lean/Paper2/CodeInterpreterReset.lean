import Paper2.LoadedTicketMachine
import EthInapproximability.CurrentPaper.BitMachineClearBank
import Mathlib.Tactic

/-! Fixed physical cleanup of a generator-interpreter workspace. The caller
must invoke this only after consuming the current ticket/header fields. -/

namespace Paper2.CodeInterpreterReset

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineClearBank

noncomputable section

abbrev Stack := LoadedTicketMachine.Stack ⊕ (Fin 7 ⊕ Fin 1)

/-- Exactly the persistent data banks across a safe repeat-step boundary. -/
def keep : Stack → Prop
  | .inl (.inl i) => i = 0 ∨ i = 11 ∨ i = 12
  | .inl (.inr _) => False
  | .inr (.inl i) => i = 0
  | .inr (.inr _) => True

abbrev ClearSlot := {k : Stack // ¬ keep k}
abbrev clearCount : Nat := Fintype.card ClearSlot

/-- A fixed enumeration of all and only the stacks to be emptied. -/
def slot (i : Fin clearCount) : Stack :=
  ((Fintype.equivFin ClearSlot).symm i).val

theorem slot_injective : Function.Injective slot := by
  intro i j h
  exact (Fintype.equivFin ClearSlot).symm.injective (Subtype.val_injective h)

theorem slot_not_keep (i : Fin clearCount) : ¬ keep (slot i) :=
  ((Fintype.equivFin ClearSlot).symm i).property

theorem exists_slot_iff (k : Stack) : (∃ i, slot i = k) ↔ ¬ keep k := by
  constructor
  · rintro ⟨i, rfl⟩
    exact slot_not_keep i
  · intro hk
    refine ⟨(Fintype.equivFin ClearSlot) ⟨k, hk⟩, ?_⟩
    simp [slot]

abbrev Label := Fin (clearCount + 1) ⊕ Unit
abbrev Control (Flag : Type) := Flag × Option Bool
abbrev Config (Flag : Type) := TM2.Cfg (fun _ : Stack => Bool) Label (Control Flag)

/-- The instruction table never branches on data or the framed flag. Each
non-kept word is popped one bit per step; the final step preserves the flag. -/
def program {Flag : Type} : Label →
    TM2.Stmt (fun _ : Stack => Bool) Label (Control Flag)
  | .inl i =>
      if h : i.val < clearCount then
        clearStep (slot ⟨i.val, h⟩) (.inl i)
          (.inl ⟨i.val + 1, by omega⟩)
      else finishStep id (.inr ())
  | .inr _ => halt

def resetBank (S : Stack → List Bool) : Stack → List Bool :=
  by
    classical
    exact fun k => if keep k then S k else []

theorem reset_kept (S : Stack → List Bool) (k : Stack) (hk : keep k) :
    resetBank S k = S k := by
  classical
  simp [resetBank, hk]

theorem reset_cleared (S : Stack → List Bool) (k : Stack) (hk : ¬ keep k) :
    resetBank S k = [] := by
  classical
  simp [resetBank, hk]

theorem reset_tape (S : Stack → List Bool) :
    resetBank S (.inl (.inl 0)) = S (.inl (.inl 0)) :=
  reset_kept S _ (by simp [keep])

theorem reset_public_B (S : Stack → List Bool) :
    resetBank S (.inl (.inl 11)) = S (.inl (.inl 11)) :=
  reset_kept S _ (by simp [keep])

theorem reset_public_R (S : Stack → List Bool) :
    resetBank S (.inl (.inl 12)) = S (.inl (.inl 12)) :=
  reset_kept S _ (by simp [keep])

theorem reset_code (S : Stack → List Bool) :
    resetBank S (.inr (.inl 0)) = S (.inr (.inl 0)) :=
  reset_kept S _ (by simp [keep])

theorem reset_output (S : Stack → List Bool) :
    resetBank S (.inr (.inr 0)) = S (.inr (.inr 0)) :=
  reset_kept S _ (by simp [keep])

theorem reset_other_outer (S : Stack → List Bool) (j : Fin 16)
    (h0 : j ≠ 0) (hB : j ≠ 11) (hR : j ≠ 12) :
    resetBank S (.inl (.inl j)) = [] :=
  reset_cleared S _ (by simp [keep, h0, hB, hR])

theorem reset_log_work (S : Stack → List Bool)
    (j : DrawParameterLoader.LogCopyStack) :
    resetBank S (.inl (.inr j)) = [] :=
  reset_cleared S _ (by simp [keep])

theorem reset_other_header (S : Stack → List Bool)
    (j : Fin 7) (hj : j ≠ 0) :
    resetBank S (.inr (.inl j)) = [] :=
  reset_cleared S _ (by simp [keep, hj])

def clock (S : Stack → List Bool) : Nat :=
  (∑ i : Fin clearCount, (S (slot i)).length) + clearCount + 2

def initial {Flag : Type} (flag : Flag) (S : Stack → List Bool) : Config Flag :=
  ⟨some (.inl 0), (flag, none), S⟩

def final {Flag : Type} (flag : Flag) (S : Stack → List Bool) : Config Flag :=
  ⟨none, (flag, none), resetBank S⟩

private theorem step_eq {Flag : Type} (i : Fin clearCount) :
    program (Flag := Flag) (.inl i.castSucc) =
      clearStep (slot i) (.inl i.castSucc) (.inl i.succ) := by
  change (if h : i.val < clearCount then
      clearStep (slot ⟨i.val, h⟩) (Sum.inl i.castSucc : Label)
        (Sum.inl ⟨i.val + 1, by omega⟩ : Label)
    else finishStep id (Sum.inr () : Label)) = _
  split_ifs with h
  · rfl
  · exact (h i.isLt).elim

private theorem finish_eq {Flag : Type} :
    program (Flag := Flag) (.inl (Fin.last clearCount)) =
      finishStep id (.inr ()) := by
  simp [program]

private theorem cleared_eq_reset (S : Stack → List Bool) :
    cleared slot S = resetBank S := by
  classical
  funext k
  by_cases hk : keep k
  · simp [cleared, resetBank, exists_slot_iff, hk]
  · simp [cleared, resetBank, exists_slot_iff, hk]

/-- Whole-bank physical run from an arbitrary ambient bank. The only retained
cells are tape, public B/R, remaining code, and accumulated output. The caller
flag is unchanged, including a failure flag. -/
theorem reset_run {Flag : Type} (flag : Flag) (S : Stack → List Bool) :
    ((advance (program (Flag := Flag)))^[clock S]) (initial flag S) =
      final flag S := by
  have hr := clear_bank_run (program (Flag := Flag)) id (.inr ())
    clearCount slot slot_injective (fun i : Fin (clearCount + 1) => (.inl i : Label))
    (by intro i; exact step_eq i) finish_eq flag S
  change ((advance (program (Flag := Flag)))^[
      (∑ i : Fin clearCount, (S (slot i)).length) + clearCount + 1])
      (initial flag S) =
    ⟨some (.inr ()), (flag, none), cleared slot S⟩ at hr
  rw [show clock S =
      ((∑ i : Fin clearCount, (S (slot i)).length) + clearCount + 1) + 1 by
        simp [clock],
      Function.iterate_succ_apply', hr]
  simp [advance, TM2.step, program, final, cleared_eq_reset]

/-- The instruction table is independent of the actual data and may be
instantiated with a Boolean success/failure bit in a finite controller. -/
abbrev boolProgram := program (Flag := Bool)

#print axioms reset_run
#print axioms reset_other_outer
#print axioms reset_log_work
#print axioms reset_other_header

end

end Paper2.CodeInterpreterReset
