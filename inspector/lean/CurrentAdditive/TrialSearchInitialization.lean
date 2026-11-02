import CurrentAdditive.TrialSearchGlobalFirst

/-! Degree-derived initial stacks for the literal search controller. -/

namespace CurrentAdditive.FieldSearchCompletion

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedSearchState
open CurrentAdditive.FieldMachineHelper.TrialCounterMachine (counterWord)

namespace Outer
open CurrentAdditive.FieldMachineHelper.TrialSearchControllerMachine
end Outer

def initialBank (d : Nat) : Fin 12 → List Bool :=
  Outer.bank (counterWord d 0) [false]
    (List.replicate (d - 1) true) (fun _ => [])
    (List.replicate (d / 2) true) [] [] []

theorem initialBank_eq_searchBank (d : Nat) (hd : 2 ≤ d) :
    initialBank d = searchBank d 0 1 0 := by
  have hhalf : 0 < d / 2 := Nat.div_pos hd (by omega)
  have hremaining : d / 2 - 1 + 1 = d / 2 := by omega
  funext i
  fin_cases i <;>
    simp [initialBank, searchBank, Outer.bank, counterWord, hremaining]

theorem initial_run_nonempty (d : Nat) (hd : 2 ≤ d)
    (base : Registers) :
    (run 1 ⟨some (.outer .initial), base, initialBank d⟩).l =
      some (.outer .test) ∧
    (run 1 ⟨some (.outer .initial), base, initialBank d⟩).stk =
      initialBank d := by
  have hhalf : 0 < d / 2 := Nat.div_pos hd (by omega)
  have h8 : initialBank d 8 = true ::
      List.replicate (d / 2 - 1) true := by
    change List.replicate (d / 2) true =
      true :: List.replicate (d / 2 - 1) true
    conv_lhs => rw [show d / 2 = (d / 2 - 1) + 1 by omega]
    simp [List.replicate_succ]
  have hstep : TM2.step program
      ⟨some (.outer .initial), base, initialBank d⟩ =
      some ⟨some (.outer .test),
        {base with outer := (base.outer.1, base.outer.2.1, some true)},
        initialBank d⟩ := by
    simp [TM2.step, TM2.stepAux, program, embedStmt,
      CurrentAdditive.FieldMachineHelper.TrialSearchControllerMachine.program,
      h8]
  simpa [run, advance, hstep]

theorem initial_run_one (base : Registers) :
    (run 1 ⟨some (.outer .initial), base, initialBank 1⟩).l =
      some (.outer .success) ∧
    (run 1 ⟨some (.outer .initial), base, initialBank 1⟩).stk 0 =
      counterWord 1 0 := by
  have h8 : initialBank 1 8 = [] := by
    simp [initialBank, Outer.bank]
  have hstep : TM2.step program
      ⟨some (.outer .initial), base, initialBank 1⟩ =
      some ⟨some (.outer .success),
        {base with outer := (base.outer.1, base.outer.2.1, none)},
        initialBank 1⟩ := by
    simp [TM2.step, TM2.stepAux, program, embedStmt,
      CurrentAdditive.FieldMachineHelper.TrialSearchControllerMachine.program,
      h8]
  have hrun : run 1 ⟨some (.outer .initial), base, initialBank 1⟩ =
      ⟨some (.outer .success),
        {base with outer := (base.outer.1, base.outer.2.1, none)},
        initialBank 1⟩ := by
    simpa [run, advance, hstep]
  rw [hrun]
  exact ⟨rfl, by simp [initialBank, Outer.bank]⟩

#print axioms initial_run_nonempty
#print axioms initial_run_one

end CurrentAdditive.FieldSearchCompletion
