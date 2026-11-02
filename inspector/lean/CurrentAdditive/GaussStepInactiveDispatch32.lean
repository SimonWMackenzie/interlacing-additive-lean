import CurrentAdditive.GaussStepFinish32

/-! Inactive branch dispatch into the checked state-packet finisher. -/

namespace CurrentAdditive.GaussStepInactiveDispatch32

noncomputable section

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding
open CurrentAdditive.GaussStepFields32

theorem inactive_dispatch (W : Stack → List Bool)
    (h25 : W 25 = [] ∨ W 25 = [false]) :
    ∃ ctrl : Control,
      run 1 ⟨some .afterBranch,eBranch ((),none),W⟩ =
        ⟨some .afterJoin,ctrl,Function.update W 25 []⟩ := by
  rcases h25 with h | h
  · refine ⟨{eBranch ((),none) with parse := none}, ?_⟩
    simp [run,program,advance,TM2.step,TM2.stepAux,h]
  · refine ⟨{eBranch ((),none) with parse := some false}, ?_⟩
    simp [run,program,advance,TM2.step,TM2.stepAux,h]

theorem prepared_clear25 (W : Stack → List Bool) :
    GaussBranchFields32.preparedBank (Function.update W 25 []) =
      GaussBranchFields32.preparedBank W := by
  funext p
  fin_cases p <;>
    simp [GaussBranchFields32.preparedBank,
      GaussBranchFields32.dest]

#print axioms inactive_dispatch
#print axioms prepared_clear25

end
end CurrentAdditive.GaussStepInactiveDispatch32
