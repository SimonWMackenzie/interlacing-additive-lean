import CurrentAdditive.RoundedCodeAdmin

/-! Complete physical workspace reset between rounded Code steps. Only the
remaining compact syntax, accumulated output, unused tape, and public width
survive. In particular the unary alphabet and all new counter/rounded work
stacks are physically cleared, so repeat entry assumes no residual emptiness.
-/

namespace EthInapproximability.CurrentPaper.RoundedCodeReset

open Turing Turing.TM2.Stmt BitMachineEncoding
open BitMachineClearBank
open scoped BigOperators
noncomputable section

abbrev Stack := RoundedCodeDraw.Stack

def code : Stack := .inl (Paper2.CodeHeaderDraw.h 0)
def output : Stack := .inl Paper2.CodeHeaderDraw.output
def tape : Stack := .inl RoundedCodeDraw.oldTape
def width : Stack := .inl RoundedCodeDraw.oldWidth

def keep (k : Stack) : Prop := k = code ∨ k = output ∨ k = tape ∨ k = width

instance (k : Stack) : Decidable (keep k) := by unfold keep; infer_instance

abbrev ClearSlot := {k : Stack // ¬ keep k}
abbrev clearCount : ℕ := Fintype.card ClearSlot

def slot (i : Fin clearCount) : Stack :=
  ((Fintype.equivFin ClearSlot).symm i).val

theorem slot_injective : Function.Injective slot := by
  intro i j h
  exact (Fintype.equivFin ClearSlot).symm.injective (Subtype.val_injective h)

theorem slot_not_keep (i : Fin clearCount) : ¬ keep (slot i) :=
  ((Fintype.equivFin ClearSlot).symm i).property

theorem exists_slot (k : Stack) : (∃ i, slot i = k) ↔ ¬ keep k := by
  constructor
  · rintro ⟨i, rfl⟩
    exact slot_not_keep i
  · intro h
    refine ⟨(Fintype.equivFin ClearSlot) ⟨k, h⟩, ?_⟩
    simp [slot]

abbrev Label := Fin (clearCount + 1) ⊕ Unit
abbrev Control (Flag : Type) := Flag × Option Bool
abbrev Config (Flag : Type) := TM2.Cfg (fun _ : Stack => Bool) Label (Control Flag)

def program {Flag : Type} : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Control Flag)
  | .inl i => if h : i.val < clearCount then
      clearStep (slot ⟨i.val, h⟩) (.inl i) (.inl ⟨i.val + 1, by omega⟩)
    else finishStep id (.inr ())
  | .inr () => halt

def resetBank (S : Stack → List Bool) : Stack → List Bool :=
  fun k => if keep k then S k else []

def clock (S : Stack → List Bool) : ℕ :=
  (∑ i : Fin clearCount, (S (slot i)).length) + clearCount + 2

theorem reset_kept (S : Stack → List Bool) (k : Stack) (h : keep k) :
    resetBank S k = S k := by simp [resetBank, h]

theorem reset_cleared (S : Stack → List Bool) (k : Stack) (h : ¬ keep k) :
    resetBank S k = [] := by simp [resetBank, h]

theorem reset_new_private (S : Stack → List Bool) (k : RoundedLoadedDraw.Stack) :
    resetBank S (.inr k) = [] := by
  apply reset_cleared
  simp [keep, code, output, tape, width]

theorem reset_alphabet (S : Stack → List Bool) :
    resetBank S (.inl RoundedCodeDraw.oldAlphabet) = [] := by
  apply reset_cleared
  simp [keep, code, output, tape, width, RoundedCodeDraw.oldAlphabet,
    RoundedCodeDraw.oldTape, RoundedCodeDraw.oldWidth,
    Paper2.CodeHeaderDraw.h, Paper2.CodeHeaderDraw.d, Paper2.CodeHeaderDraw.output]

theorem physical_reset {Flag : Type} (flag : Flag) (S : Stack → List Bool) :
    ((advance (program (Flag := Flag)))^[clock S])
      (⟨some (.inl 0), (flag, none), S⟩ : Config Flag) =
        ⟨none, (flag, none), resetBank S⟩ := by
  have hsteps (i : Fin clearCount) : program (Flag := Flag) (.inl i.castSucc) =
      clearStep (slot i) (.inl i.castSucc) (.inl i.succ) := by
    simp only [program]
    split_ifs with h
    · rfl
    · exact (h i.isLt).elim
  have hfinish : program (Flag := Flag) (.inl (Fin.last clearCount)) =
      finishStep id (.inr ()) := by simp [program]
  have hr := clear_bank_run (program (Flag := Flag)) id (.inr ()) clearCount
    slot slot_injective (fun i => (.inl i : Label)) hsteps hfinish flag S
  have hbank : cleared slot S = resetBank S := by
    funext k
    by_cases h : keep k <;> simp [cleared, resetBank, exists_slot, h]
  rw [show clock S =
      ((∑ i : Fin clearCount, (S (slot i)).length) + clearCount + 1) + 1 by
        simp [clock], Function.iterate_succ_apply', hr]
  simp [advance, TM2.step, program, hbank]

/-- The resource hypothesis bounds the initial scratch words only. The final
scratch size is derived from the literal predecessor program's stack growth,
and all of it is charged by the physical reset theorem above. -/
theorem clock_le_of_run {L V : Type*} [Fintype L]
    (P : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (c : TM2.Cfg (fun _ : Stack => Bool) L V) (t : ℕ) (maxInitial : ℕ)
    (hInitial : ∀ i : Fin clearCount, (c.stk (slot i)).length ≤ maxInitial) :
    clock (((advance P)^[t]) c).stk ≤
      clearCount * (maxInitial + BitMachineStackGrowth.perStep P * t) + clearCount + 2 := by
  have hc (i : Fin clearCount) :
      ((((advance P)^[t]) c).stk (slot i)).length ≤
        maxInitial + BitMachineStackGrowth.perStep P * t :=
    (BitMachineStackGrowth.run_growth P c t (slot i)).trans
      (Nat.add_le_add_right (hInitial i) _)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hc i)
  simpa [clock, Finset.sum_const, Fintype.card_fin, smul_eq_mul] using
    Nat.add_le_add_right (Nat.add_le_add_right hs clearCount) 2

#print axioms physical_reset
#print axioms clock_le_of_run
#print axioms reset_new_private

end
end EthInapproximability.CurrentPaper.RoundedCodeReset
