import Paper2.TemplateStepX
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-! Unit 3, segment (2) enabler: a UNIFORM per-step growth bound for the ONE
fixed program `TemplateStepX.stepX`. The admitted
`BitMachineStackGrowth.run_growth` needs `Fintype` of the program's label
type; the label type of `stepX` is a finite nesting of sums of label types,
six of which (production `OutputSkipper.Admin`, `FetchLabel.Label`; frozen
owner-4 `SourcePos.PL`, `ScanSelect.SLabel`, `RankRun.SL`; frozen owner-5
`OTOps.CL`) carry no `Fintype` instance. They are finite enumerations (or
finite sums of such); the instances are derived here (instances only; no
definition is changed). Consequence (`stepX_growth`, `exit_length_le`): every
cell's length after `t` steps of `stepX` is at most its entry length plus
`perStep stepX * t`, with `perStep stepX` a constant (independent of the
level, the pair, the graph). This is the length bound needed to clear the
existential scratch cells (`r1 tagC`, `myJ`, the placed cells, `E`) with a
uniform clock (`OTOps.clr_run`: `|cell| + 1` steps). -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.StepXGrowth

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackGrowth

deriving instance Fintype for Paper2.OutputSkipper.Admin
deriving instance Fintype for Paper2.FetchLabel.Label
deriving instance Fintype for Paper2.SourcePos.PL
deriving instance Fintype for Paper2.ScanSelect.SLabel
deriving instance Fintype for Paper2.RankRun.SL
deriving instance Fintype for Paper2.OTOps.CL

/-- The per-step push bound of the ONE fixed program `stepX` (a constant). -/
noncomputable def pushBound : ℕ := perStep TemplateStepX.stepX

theorem stepX_growth (c : TM2.Cfg (fun _ : TemplateStepX.JT => Bool) _ _) (t : ℕ)
    (j : TemplateStepX.JT) :
    ((((advance TemplateStepX.stepX)^[t]) c).stk j).length ≤ (c.stk j).length + pushBound * t :=
  run_growth TemplateStepX.stepX c t j

/-- Exit-cell length bound for any halting run of `stepX` within `T` steps. -/
theorem exit_length_le (c : TM2.Cfg (fun _ : TemplateStepX.JT => Bool) _ _) (t T : ℕ) (hT : t ≤ T)
    (v : _) (F : TemplateStepX.JT → List Bool)
    (h : ((advance TemplateStepX.stepX)^[t]) c = ⟨none, v, F⟩) (j : TemplateStepX.JT) :
    (F j).length ≤ (c.stk j).length + pushBound * T := by
  have g := stepX_growth c t j
  rw [h] at g
  have : pushBound * t ≤ pushBound * T := Nat.mul_le_mul_left _ hT
  exact g.trans (by simpa using this)

end Paper2.StepXGrowth

#print axioms Paper2.StepXGrowth.stepX_growth
#print axioms Paper2.StepXGrowth.exit_length_le
