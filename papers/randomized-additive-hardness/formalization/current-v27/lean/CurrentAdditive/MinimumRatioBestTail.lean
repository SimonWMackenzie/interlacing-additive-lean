import CurrentAdditive.MinimumRatioCallbackCalls

namespace CurrentAdditive.MinimumRatioBestTail

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioCallbackLayout

noncomputable def copySlots : Fin 3 ↪ Stack where
  toFun i := low (![9,20,21] i)
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [low]

noncomputable def copyProgram := ExactParameterBranchInstall.copyProgram copySlots

theorem copy_run (S : Bank) (best : List Bool)
    (h9 : S (low 9) = best)
    (h20 : S (low 20) = [])
    (h21 : S (low 21) = []) :
    ∃ u ≤ 2*best.length+2,
      ((advance copyProgram)^[u])
        (⟨some BitMachineCopy.Label.scan, none, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, none, Function.update S (low 20) best⟩ := by
  simpa [copyProgram, copySlots] using
    ExactParameterBranchInstall.copy_run copySlots S best
      (by simpa [copySlots] using h9)
      (by simpa [copySlots] using h20)
      (by simpa [copySlots] using h21)

noncomputable def tailProgram : Unit → TM2.Stmt (fun _ : Stack => Bool) Unit (Option Bool)
  | () => .pop (low 20) (fun _ b => b) .halt

theorem tail_run (S : Bank) :
    ((advance tailProgram)^[1])
      (⟨some (), none, S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, (S (low 20)).head?,
        Function.update S (low 20) (S (low 20)).tail⟩ := by
  simp [advance, tailProgram, TM2.step, TM2.stepAux]

end CurrentAdditive.MinimumRatioBestTail
