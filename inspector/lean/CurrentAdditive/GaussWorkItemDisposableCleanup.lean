import CurrentAdditive.GaussWorkItemCleanup

/-! Reset all three disposable Bank3 operand banks after the serialized
callback.  This removes any dependence on the serializer's unspecified
residual word bank and makes the next iteration's blank-bank premises exact. -/

namespace CurrentAdditive.GaussWorkItemDisposableCleanup

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding

abbrev Bank := GaussWorkItemCleanup.Bank

inductive Label where
  | matrix | free | index | finish | halt
  deriving DecidableEq, Fintype

def cells : Fin 3 → Bank :=
  ![⟨9, by omega⟩, ⟨10, by omega⟩, ⟨11, by omega⟩]

theorem cells_injective : Function.Injective cells := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [cells]

def label : Fin 4 → Label := ![.matrix, .free, .index, .finish]

def program : Label → TM2.Stmt (fun _ : Bank => Bool) Label (Unit × Option Bool)
  | .matrix => BitMachineClearBank.clearStep (cells 0) .matrix .free
  | .free => BitMachineClearBank.clearStep (cells 1) .free .index
  | .index => BitMachineClearBank.clearStep (cells 2) .index .finish
  | .finish => BitMachineClearBank.finishStep id .halt
  | .halt => .halt

theorem cleared_at (S : Bank → List Bool) (i : Fin 3) :
    BitMachineClearBank.cleared cells S (cells i) = [] :=
  BitMachineClearBank.cleared_bank cells S i

theorem cleared_foreign (S : Bank → List Bool) (z : Bank)
    (hz : z ≠ ⟨9, by omega⟩ ∧ z ≠ ⟨10, by omega⟩ ∧
      z ≠ ⟨11, by omega⟩) :
    BitMachineClearBank.cleared cells S z = S z := by
  apply BitMachineClearBank.cleared_foreign
  intro i
  fin_cases i <;> simp [cells, Ne.symm hz.1, Ne.symm hz.2.1,
    Ne.symm hz.2.2]

theorem physical_cleanup (S : Bank → List Bool) :
    ((advance program)^[(S ⟨9, by omega⟩).length +
        (S ⟨10, by omega⟩).length +
        (S ⟨11, by omega⟩).length + 5])
      (⟨some .matrix, ((), none), S⟩ :
        TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none, ((), none), BitMachineClearBank.cleared cells S⟩ := by
  have hsteps : ∀ i : Fin 3,
      program (label i.castSucc) =
        BitMachineClearBank.clearStep (cells i)
          (label i.castSucc) (label i.succ) := by
    intro i
    fin_cases i <;> rfl
  have hfinish : program (label (Fin.last 3)) =
      BitMachineClearBank.finishStep id Label.halt := rfl
  have hr := BitMachineClearBank.clear_bank_run program id Label.halt
    3 cells cells_injective label hsteps hfinish () S
  have hr' :
      ((advance program)^[(∑ i : Fin 3, (S (cells i)).length) + 3 + 1])
        (⟨some .matrix, ((), none), S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨some .halt, ((), none), BitMachineClearBank.cleared cells S⟩ := by
    simpa [label] using hr
  have htime : (∑ i : Fin 3, (S (cells i)).length) + 3 + 1 + 1 =
      (S ⟨9, by omega⟩).length + (S ⟨10, by omega⟩).length +
        (S ⟨11, by omega⟩).length + 5 := by
    simp [cells, Fin.sum_univ_succ]
    omega
  rw [← htime]
  rw [show (∑ i : Fin 3, (S (cells i)).length) + 3 + 1 + 1 =
      1 + ((∑ i : Fin 3, (S (cells i)).length) + 3 + 1) by omega,
    Function.iterate_add_apply, Function.iterate_one, hr']
  simp [advance, TM2.step, program, TM2.stepAux]

#print axioms physical_cleanup

end CurrentAdditive.GaussWorkItemDisposableCleanup
