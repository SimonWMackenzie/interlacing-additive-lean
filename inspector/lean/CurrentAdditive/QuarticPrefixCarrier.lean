import Paper2.E6Tape
import CurrentAdditive.QuarticSourceSizeNumeric

/-!
An R20 algorithm constructor for a fixed machine whose output reads a
bounded prefix of a precommitted tape. The same physical run proves R22
extension invariance.
-/

noncomputable section

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity
open Paper2 Paper2.AEth2 Paper2.AEth4

def prefixCarrier27 (c a : ℕ) (M : BitMachine.Machine)
    (T R : List Bool → ℕ) (F : List Bool → List Bool → List Bool)
    (hfit : ∀ x, R x ≤ tapeCA c a x.length)
    (hrun : ∀ x t, R x ≤ t.length →
      M.OutputsWithin (pair x t) (F x (t.take (R x))) (T x)) :
    ETape.Algorithm where
  tapeLen := tapeCA c a
  lenMachine := CAMachine c a
  lenTime := CAtime c a
  lenC := (BT + 30) * (c + 1) ^ 2
  lenE := 2
  lenRuns := CAMachine_outputs c a
  lenPoly := CAtime_poly c a
  tapeSubexp := tapeCA_subexp c a
  machine := M
  time := T
  output := fun x t => F x (t.take (R x))
  runs := by
    intro x t
    exact hrun x (List.ofFn t) (by simpa using hfit x)
  extend := by
    intro x t u ht
    have hR : R x ≤ t.length := by simpa [ht] using hfit x
    have hprefix : (t ++ u).take (R x) = t.take (R x) :=
      List.take_append_of_le_length hR
    rw [show F x (t.take (R x)) =
      F x ((t ++ u).take (R x)) by rw [hprefix]]
    exact hrun x (t ++ u) (by rw [List.length_append]; omega)

#print axioms prefixCarrier27

end Paper2.CurrentAdditive.QuarticClassEndpoint

end
