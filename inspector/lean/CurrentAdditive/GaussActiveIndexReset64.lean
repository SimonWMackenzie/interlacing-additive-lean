import CurrentAdditive.GaussFetchSave64

/-! Charged clearing of the two active unary getter-index banks. -/

namespace CurrentAdditive.GaussActiveIndexReset64

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 64

inductive Label where
  | clear : Fin 2 → Label
  | finish | done
  deriving DecidableEq, Fintype

abbrev Control := Unit × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def bank : Fin 2 → Stack := ![15, 16]

def nextClear (i : Fin 2) : Label :=
  if h : i.val + 1 < 2 then .clear ⟨i.val + 1, h⟩ else .finish

def clearLabel (i : Fin 3) : Label :=
  if h : i.val < 2 then .clear ⟨i.val, h⟩ else .finish

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .clear i => BitMachineClearBank.clearStep (bank i)
      (.clear i) (nextClear i)
  | .finish => BitMachineClearBank.finishStep id .done
  | .done => .halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

def cleared (S : Stack → List Bool) : Stack → List Bool :=
  BitMachineClearBank.cleared bank S

theorem bank_injective : Function.Injective bank := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [bank]

theorem clearLabel_step (i : Fin 2) :
    clearLabel i.castSucc = .clear i ∧
    clearLabel i.succ = nextClear i := by
  fin_cases i <;> simp [clearLabel, nextClear]

theorem clearLabel_finish : clearLabel (Fin.last 2) = .finish := by
  simp [clearLabel]

theorem reset_run (S : Stack → List Bool) :
    run ((S 15).length + (S 16).length + 3)
      ⟨some (.clear 0), ((), none), S⟩ =
      ⟨some .done, ((), none), cleared S⟩ := by
  have hsum : (∑ i : Fin 2, (S (bank i)).length) =
      (S 15).length + (S 16).length := by
    simp [Fin.sum_univ_two, bank]
  rw [← hsum]
  change ((advance program)^[(∑ i : Fin 2,
      (S (bank i)).length) + 2 + 1])
    ⟨some (clearLabel 0), ((), none), S⟩ = _
  apply BitMachineClearBank.clear_bank_run program id .done
    2 bank bank_injective clearLabel
  · intro i
    obtain ⟨hi, hn⟩ := clearLabel_step i
    rw [hi, hn]
    rfl
  · rw [clearLabel_finish]
    rfl

theorem cleared_active (S : Stack → List Bool) (i : Fin 2) :
    cleared S (bank i) = [] := by
  simp [cleared, BitMachineClearBank.cleared,
    show ∃ j : Fin 2, bank j = bank i from ⟨i, rfl⟩]

theorem cleared_other (S : Stack → List Bool) (j : Stack)
    (hj15 : j ≠ 15) (hj16 : j ≠ 16) :
    cleared S j = S j := by
  simp only [cleared, BitMachineClearBank.cleared]
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    fin_cases i <;> simp [bank] at hi
    · exact False.elim (hj15 hi.symm)
    · exact False.elim (hj16 hi.symm)
  · rfl

#print axioms reset_run
#print axioms cleared_active
#print axioms cleared_other

end CurrentAdditive.GaussActiveIndexReset64
