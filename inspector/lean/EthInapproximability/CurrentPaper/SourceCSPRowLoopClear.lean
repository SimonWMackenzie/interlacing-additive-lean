import EthInapproximability.CurrentPaper.SourceCSPRowQueryUnary
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-!
# Reusable row-query bank reset

The source suffix stays in shared cell `.inr 0`. Every query/input/work cell
and the four other shared cells are physically popped before the next row.
Four outer stacks retain the unary row counter and the immutable cap.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopClear

open Turing BitMachineEncoding

abbrev Stack (q : Nat) := SourceCSPRowQueryFrame.Stack q ⊕ Fin 4

def scratchEquiv (q : Nat) : Fin (q * 5 + 4) ≃ (Fin q × Fin 5) ⊕ Fin 4 :=
  (finSumFinEquiv).symm.trans
    (Equiv.sumCongr finProdFinEquiv.symm (Equiv.refl (Fin 4)))

def scratchSlot {q : Nat} : (Fin q × Fin 5) ⊕ Fin 4 → Stack q
  | .inl p => .inl (.inl p)
  | .inr i => .inl (.inr ⟨i.val + 1, by omega⟩)

theorem scratchSlot_injective {q : Nat} : Function.Injective (scratchSlot (q := q)) := by
  intro x y h
  cases x with
  | inl p =>
    cases y with
    | inl r => exact congrArg Sum.inl (Sum.inl.inj (Sum.inl.inj h))
    | inr r => cases h
  | inr p =>
    cases y with
    | inl r => cases h
    | inr r =>
      apply congrArg Sum.inr
      apply Fin.ext
      have hv := congrArg Fin.val (Sum.inr.inj (Sum.inl.inj h))
      dsimp [scratchSlot] at hv
      omega

def scratch (q : Nat) : Fin (q * 5 + 4) ↪ Stack q :=
  ⟨scratchSlot ∘ scratchEquiv q, scratchSlot_injective.comp (scratchEquiv q).injective⟩

abbrev Label (q : Nat) := Fin (q * 5 + 6)
abbrev Control := Unit × Option Bool
abbrev Config (q : Nat) := TM2.Cfg (fun _ : Stack q => Bool) (Label q) Control

def labels (q : Nat) (i : Fin (q * 5 + 5)) : Label q := ⟨i.val, by omega⟩

def program (q : Nat) (l : Label q) :
    TM2.Stmt (fun _ : Stack q => Bool) (Label q) Control :=
  if h : l.val < q * 5 + 4 then
    BitMachineClearBank.clearStep (scratch q ⟨l.val, h⟩) l
      ⟨l.val + 1, by omega⟩
  else if l.val = q * 5 + 4 then
    BitMachineClearBank.finishStep id ⟨q * 5 + 5, by omega⟩
  else .halt

theorem run_clear (q : Nat) (S : Stack q → List Bool) :
    ((advance (program q))^[(∑ i : Fin (q * 5 + 4),
      (S (scratch q i)).length) + (q * 5 + 4) + 1])
      (⟨some 0, ((), none), S⟩ : Config q) =
    ⟨some ⟨q * 5 + 5, by omega⟩, ((), none),
      BitMachineClearBank.cleared (scratch q) S⟩ := by
  apply BitMachineClearBank.clear_bank_run (program q) id
    ⟨q * 5 + 5, by omega⟩ (q * 5 + 4) (scratch q)
    (scratch q).injective (labels q)
  · intro i
    simp [program, labels]
  · simp [program, labels]

theorem run_halt (q : Nat) (S : Stack q → List Bool) :
    ((advance (program q))^[(∑ i : Fin (q * 5 + 4),
      (S (scratch q i)).length) + (q * 5 + 4) + 2])
      (⟨some 0, ((), none), S⟩ : Config q) =
    ⟨none, ((), none), BitMachineClearBank.cleared (scratch q) S⟩ := by
  rw [show (∑ i : Fin (q * 5 + 4), (S (scratch q i)).length) +
      (q * 5 + 4) + 2 =
      1 + ((∑ i : Fin (q * 5 + 4), (S (scratch q i)).length) +
        (q * 5 + 4) + 1) by omega,
    Function.iterate_add_apply, run_clear]
  simp [advance, TM2.step, program, TM2.stepAux]

end EthInapproximability.CurrentPaper.SourceCSPRowLoopClear
