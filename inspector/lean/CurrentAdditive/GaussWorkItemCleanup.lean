import CurrentAdditive.GaussWorkItemAccumulator
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-! Explicitly clear the raw item and framed item banks after prepending the
field to the output accumulator.  This makes the per-column callback reusable. -/

namespace CurrentAdditive.GaussWorkItemCleanup

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding

abbrev Bank := GaussWorkItemAccumulator.Bank

inductive Label where
  | raw | field | finish | halt
  deriving DecidableEq, Fintype

def cells : Fin 2 → Bank := ![⟨8, by omega⟩, ⟨13, by omega⟩]

theorem cells_injective : Function.Injective cells := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [cells]

def label : Fin 3 → Label := ![.raw, .field, .finish]

def program : Label → TM2.Stmt (fun _ : Bank => Bool) Label (Unit × Option Bool)
  | .raw => BitMachineClearBank.clearStep (cells 0) .raw .field
  | .field => BitMachineClearBank.clearStep (cells 1) .field .finish
  | .finish => BitMachineClearBank.finishStep id .halt
  | .halt => .halt

theorem cleared_eq (S : Bank → List Bool) :
    BitMachineClearBank.cleared cells S =
      Function.update (Function.update S ⟨8, by omega⟩ [])
        ⟨13, by omega⟩ [] := by
  funext z
  by_cases h8 : z = (⟨8, by omega⟩ : Bank)
  · subst z; simp [BitMachineClearBank.cleared, cells]
  by_cases h13 : z = (⟨13, by omega⟩ : Bank)
  · subst z; simp [BitMachineClearBank.cleared, cells]
  have hn : ¬ ∃ i : Fin 2, cells i = z := by
    rintro ⟨i, hi⟩
    fin_cases i
    · exact h8 hi.symm
    · exact h13 hi.symm
  simp [BitMachineClearBank.cleared, hn, h8, h13]

theorem physical_cleanup (S : Bank → List Bool) :
    ((advance program)^[(S ⟨8, by omega⟩).length +
        (S ⟨13, by omega⟩).length + 4])
      (⟨some .raw, ((), none), S⟩ :
        TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none, ((), none),
        Function.update (Function.update S ⟨8, by omega⟩ [])
          ⟨13, by omega⟩ []⟩ := by
  have hsteps : ∀ i : Fin 2,
      program (label i.castSucc) =
        BitMachineClearBank.clearStep (cells i)
          (label i.castSucc) (label i.succ) := by
    intro i
    fin_cases i <;> rfl
  have hfinish : program (label (Fin.last 2)) =
      BitMachineClearBank.finishStep id Label.halt := rfl
  have hr := BitMachineClearBank.clear_bank_run program id Label.halt
    2 cells cells_injective label hsteps hfinish () S
  have hr' :
      ((advance program)^[(∑ i : Fin 2, (S (cells i)).length) + 2 + 1])
        (⟨some .raw, ((), none), S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨some .halt, ((), none), BitMachineClearBank.cleared cells S⟩ := by
    simpa [label] using hr
  have htime : (∑ i : Fin 2, (S (cells i)).length) + 2 + 1 + 1 =
      (S ⟨8, by omega⟩).length + (S ⟨13, by omega⟩).length + 4 := by
    simp [cells, Fin.sum_univ_succ]
  rw [← htime]
  rw [show (∑ i : Fin 2, (S (cells i)).length) + 2 + 1 + 1 =
      1 + ((∑ i : Fin 2, (S (cells i)).length) + 2 + 1) by omega,
    Function.iterate_add_apply, Function.iterate_one]
  rw [hr']
  simp [advance, TM2.step, program, TM2.stepAux, cleared_eq]

#print axioms physical_cleanup

end CurrentAdditive.GaussWorkItemCleanup
