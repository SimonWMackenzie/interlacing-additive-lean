import Paper2.HeaderEvent
import Paper2.HeaderClassifierSelected

/-!
# Pointwise classifier on the physical fixed-gap header output

This combines the exact output-stack identity of `HeaderWordRun.machine` with
the previously checked selected-tape strip/median/comparator. The source
estimator guarantee and the matrix's target cost remain explicit hypotheses;
no source-front sampler or SAT reduction is supplied by this file.
-/

noncomputable section

namespace Paper2.HeaderWordRun

open EthInapproximability.CurrentPaper.EncodedCommunication

theorem classifier_yes_on_printed_output
    (A : Paper2.SelectedTape.Algorithm) (a : ℝ)
    (hA : ∀ w c, Paper2.AModel.targetD w = some c →
      2 / 3 ≤ A.prob w (fun out => ∃ v,
        Paper2.AModel.decodeDyadic out = some v ∧ |v - c| ≤ a))
    (i : Instance) (k c : ℕ)
    (hk : 0 < k) (htarget : Paper2.AModel.targetD (matrix i) = some c)
    (hgap : 2 * a < k) (hcost : c ≤ i.threshold) :
    99 / 100 ≤ (Paper2.HeaderStrip.selectedClassifier A).prob
      (printedAtClock k i) (· = [true]) := by
  rw [printedAtClock_eq k i hk]
  exact Paper2.HeaderStrip.selectedClassifier_yes A a hA
    (matrix i) c i.threshold k htarget hgap hcost

theorem classifier_no_on_printed_output
    (A : Paper2.SelectedTape.Algorithm) (a : ℝ)
    (hA : ∀ w c, Paper2.AModel.targetD w = some c →
      2 / 3 ≤ A.prob w (fun out => ∃ v,
        Paper2.AModel.decodeDyadic out = some v ∧ |v - c| ≤ a))
    (i : Instance) (k c : ℕ)
    (hk : 0 < k) (htarget : Paper2.AModel.targetD (matrix i) = some c)
    (hgap : 2 * a < k) (hcost : i.threshold + k ≤ c) :
    (Paper2.HeaderStrip.selectedClassifier A).prob
      (printedAtClock k i) (· = [true]) ≤ 1 / 100 := by
  rw [printedAtClock_eq k i hk]
  exact Paper2.HeaderStrip.selectedClassifier_no A a hA
    (matrix i) c i.threshold k htarget hgap hcost

#print axioms classifier_yes_on_printed_output
#print axioms classifier_no_on_printed_output

end Paper2.HeaderWordRun
