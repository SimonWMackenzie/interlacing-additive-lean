import Paper2.HeaderStrip
import Paper2.SelectedTapeAdapters
import Paper2.AModelEstimator

/-!
# Header stripping for the selected-pair fixed-tape model

Unlike the stronger all-code carrier, this estimator assumes a machine clock
only on correctly paired inputs with its selected monomial-length tape.  The
physical `SelectedTape.pullback` closes the preprocessing/composition clock on
that same selected tape; it does not assume arbitrary tape-length advice.
-/

noncomputable section

namespace Paper2.HeaderStrip

open EthInapproximability.CurrentPaper

/-- The actual physical preprocessing and selected-tape composition. -/
def selectedEstimator (A : Paper2.SelectedTape.Algorithm) :
    Paper2.SelectedTape.Algorithm :=
  Paper2.SelectedTape.pullback strip polytime A

theorem selectedEstimator_output (A : Paper2.SelectedTape.Algorithm) (n : ℕ)
    (rest tape : List Bool) :
    (selectedEstimator A).output (EncodedCommunication.natField n ++ rest) tape =
      A.output rest (tape.take (A.tapeLength rest)) := by
  rw [selectedEstimator, Paper2.SelectedTape.pullback_output, strip_natField]

/-- The uniform output-event law is exactly the matrix-word law. -/
theorem selectedEstimator_prob (A : Paper2.SelectedTape.Algorithm) (n : ℕ)
    (rest : List Bool) (E : List Bool → Prop) :
    (selectedEstimator A).prob (EncodedCommunication.natField n ++ rest) E =
      A.prob rest E := by
  rw [selectedEstimator, Paper2.SelectedTape.pullback_prob, strip_natField]

theorem selectedEstimator_toPrefix_prob (A : Paper2.SelectedTape.Algorithm) (n : ℕ)
    (rest : List Bool) (E : List Bool → Prop) :
    (selectedEstimator A).toPrefix.prob
      (EncodedCommunication.natField n ++ rest) E = A.prob rest E := by
  rw [Paper2.SelectedTape.Algorithm.toPrefix_prob, selectedEstimator_prob]

theorem selectedEstimator_toPrefix_polynomial (A : Paper2.SelectedTape.Algorithm) :
    (selectedEstimator A).toPrefix.Polynomial :=
  Paper2.SelectedTape.Algorithm.toPrefix_polynomial (selectedEstimator A)

/-- Matrix-only D-A3 success is exactly the success hypothesis for the
comparator's threshold-prefixed word. -/
theorem selectedEstimator_estimatesD (A : Paper2.SelectedTape.Algorithm) (a : ℝ)
    (hA : ∀ w c, Paper2.AModel.targetD w = some c →
      2 / 3 ≤ A.prob w (fun out => ∃ v,
        Paper2.AModel.decodeDyadic out = some v ∧ |v - c| ≤ a))
    (n : ℕ) (rest : List Bool) (c : ℕ)
    (hc : Paper2.AModel.targetD rest = some c) :
    2 / 3 ≤ (selectedEstimator A).toPrefix.prob
      (EncodedCommunication.natField n ++ rest)
      (fun out => ∃ v, Paper2.AModel.decodeDyadic out = some v ∧ |v - c| ≤ a) := by
  rw [selectedEstimator_toPrefix_prob]
  exact hA rest c hc

#print axioms selectedEstimator_output
#print axioms selectedEstimator_prob
#print axioms selectedEstimator_toPrefix_polynomial
#print axioms selectedEstimator_estimatesD

end Paper2.HeaderStrip
