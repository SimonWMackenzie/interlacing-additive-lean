import CurrentAdditive.V39RequestStepK
import Paper2.StepXGrowth

set_option synthInstance.maxSize 16384
set_option maxRecDepth 16384

namespace CurrentAdditive.V39RLoopGrowth

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-- The per-step push bound of the ONE fixed program `stepX` (a constant). -/
noncomputable def pushBound : ℕ := perStep CurrentAdditive.V39RequestStep.stepX

theorem stepX_growth (c : TM2.Cfg (fun _ : Paper2.TemplateStepX.JT => Bool) _ _) (t : ℕ)
    (j : Paper2.TemplateStepX.JT) :
    ((((advance CurrentAdditive.V39RequestStep.stepX)^[t]) c).stk j).length ≤ (c.stk j).length + pushBound * t :=
  run_growth CurrentAdditive.V39RequestStep.stepX c t j

/-- Exit-cell length bound for any halting run of `stepX` within `T` steps. -/
theorem exit_length_le (c : TM2.Cfg (fun _ : Paper2.TemplateStepX.JT => Bool) _ _) (t T : ℕ) (hT : t ≤ T)
    (v : _) (F : Paper2.TemplateStepX.JT → List Bool)
    (h : ((advance CurrentAdditive.V39RequestStep.stepX)^[t]) c = ⟨none, v, F⟩) (j : Paper2.TemplateStepX.JT) :
    (F j).length ≤ (c.stk j).length + pushBound * T := by
  have g := stepX_growth c t j
  rw [h] at g
  have : pushBound * t ≤ pushBound * T := Nat.mul_le_mul_left _ hT
  exact g.trans (by simpa using this)

end CurrentAdditive.V39RLoopGrowth

#print axioms CurrentAdditive.V39RLoopGrowth.stepX_growth
#print axioms CurrentAdditive.V39RLoopGrowth.exit_length_le
