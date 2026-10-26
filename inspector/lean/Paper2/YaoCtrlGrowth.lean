import Paper2.YaoUniformClock
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-! Lane a-yao-owner-1, Y5 prerequisite: a uniform per-step growth bound for
the ONE fixed ported controller `fullEntryProgram t lambda` (admitted
`BitMachineStackGrowth.run_growth`).  With `controller_bound_le_uniform`, every
exit cell of the controller has length at most its entry length plus
`perStep (fullEntryProgram t lambda) * controllerUniform t lambda e`: the
length bound a uniform-clock cleanup of the controller's existential scratch
needs.  No machine is built here. -/

namespace Paper2.YaoCtrlGrowth

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackGrowth
open Paper2.YaoEntryControllerJoin

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

noncomputable instance fullLabelFintype (t lambda : ℕ) : Fintype (FullLabel t lambda) := by
  unfold FullLabel LoadedLabel LiftLoaderLabel LoaderLabel
  infer_instance

theorem controller_growth (t lambda : ℕ)
    (c : TM2.Cfg (fun _ : InputStack t lambda => Bool) (FullLabel t lambda)
      (FullControl t lambda)) (n : ℕ) (j : InputStack t lambda) :
    ((((advance (fullEntryProgram t lambda))^[n]) c).stk j).length ≤
      (c.stk j).length + perStep (fullEntryProgram t lambda) * n :=
  run_growth (fullEntryProgram t lambda) c n j

/-- Exit-cell length bound for any halting controller run within `T` steps. -/
theorem controller_exit_length_le (t lambda : ℕ)
    (c : TM2.Cfg (fun _ : InputStack t lambda => Bool) (FullLabel t lambda)
      (FullControl t lambda)) (n T : ℕ) (hn : n ≤ T) (v : FullControl t lambda)
    (F : InputStack t lambda → List Bool)
    (h : ((advance (fullEntryProgram t lambda))^[n]) c = ⟨none, v, F⟩) (j : InputStack t lambda) :
    (F j).length ≤ (c.stk j).length + perStep (fullEntryProgram t lambda) * T := by
  have g := controller_growth t lambda c n j
  rw [h] at g
  exact g.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hn) _)

#print axioms controller_growth
#print axioms controller_exit_length_le

end Paper2.YaoCtrlGrowth
