import CurrentAdditive.GaussGetterSafe64
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-! Charged reset of every writable stack of the safe Fin64 getter except
the preserved matrix bank 8. The caller's source/output/index/context/fuel
banks and operand backups remain untouched. -/

namespace CurrentAdditive.GaussGetterReset64

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 64

inductive Label where
  | clear : Fin 21 → Label
  | finish | done
  deriving DecidableEq, Fintype

abbrev Control := Unit × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def resetBank : Fin 21 → Stack :=
  ![32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42,
    43, 44, 45, 46, 47, 48, 49, 50, 51, 52]

def nextClear (j : Fin 21) : Label :=
  if h : j.val + 1 < 21 then .clear ⟨j.val + 1, h⟩
  else .finish

def clearLabel : Fin 22 → Label :=
  fun j => if h : j.val < 21 then .clear ⟨j.val, h⟩ else .finish

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .clear j => BitMachineClearBank.clearStep (resetBank j)
      (.clear j) (nextClear j)
  | .finish => BitMachineClearBank.finishStep id .done
  | .done => .halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem resetBank_injective : Function.Injective resetBank := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [resetBank]

theorem clearLabel_step (i : Fin 21) :
    clearLabel i.castSucc = .clear i ∧
    clearLabel i.succ = nextClear i := by
  fin_cases i <;> simp [clearLabel, nextClear]

theorem clearLabel_finish : clearLabel (Fin.last 21) = .finish := by
  simp [clearLabel]

theorem reset_run (S : Stack → List Bool) :
    run ((∑ i : Fin 21, (S (resetBank i)).length) + 22)
      ⟨some (.clear 0), ((), none), S⟩ =
      ⟨some .done, ((), none),
       BitMachineClearBank.cleared resetBank S⟩ := by
  change ((advance program)^[(∑ i : Fin 21,
      (S (resetBank i)).length) + 21 + 1])
    ⟨some (clearLabel 0), ((), none), S⟩ = _
  apply BitMachineClearBank.clear_bank_run program id .done
    21 resetBank resetBank_injective clearLabel
  · intro i
    obtain ⟨hi, hn⟩ := clearLabel_step i
    rw [hi, hn]
    rfl
  · rw [clearLabel_finish]
    rfl

theorem reset_clears (S : Stack → List Bool) (i : Fin 21) :
    (BitMachineClearBank.cleared resetBank S) (resetBank i) = [] := by
  simp [BitMachineClearBank.cleared,
    show ∃ j : Fin 21, resetBank j = resetBank i from ⟨i, rfl⟩]

theorem reset_preserves (S : Stack → List Bool) (j : Stack)
    (h : j.val < 32 ∨ 53 ≤ j.val) :
    (BitMachineClearBank.cleared resetBank S) j = S j := by
  simp only [BitMachineClearBank.cleared]
  split_ifs with he
  · obtain ⟨i, hi⟩ := he
    have hv := congrArg Fin.val hi
    have hs : 32 ≤ (resetBank i).val ∧
        (resetBank i).val < 53 := by
      fin_cases i <;> decide
    rcases h with hsmall | hlarge <;> omega
  · rfl

#print axioms reset_run
#print axioms reset_preserves

end CurrentAdditive.GaussGetterReset64
