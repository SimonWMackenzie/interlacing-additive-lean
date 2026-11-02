import Paper2.HeaderEstimatorSelected
import Paper2.CmpMedian

/-!
# Comparator coupling on the intended selected-pair fixed-tape carrier

The original D-A3 estimator receives only a matrix word.  `selectedEstimator`
physically strips the leading midpoint field, chooses a fixed monomial outer
tape, truncates to the inner tape and runs the original estimator.  Thus the
checked median/comparator machine sees the full header-prefixed input while
the estimator guarantee is invoked only on the original matrix word.
-/

noncomputable section

namespace Paper2.HeaderStrip

open EthInapproximability.CurrentPaper.EncodedCommunication

def selectedMedianDecision (A : Paper2.SelectedTape.Algorithm) :
    Paper2.AModel.PrefixAlgorithm :=
  Paper2.CmpOwner.medAlgC ((selectedEstimator A).toPrefix)

/-- The median's tape is literally a fixed monomial: `reps` disjoint
copies of the selected strip-estimator tape. This is the input to the
generic selected-carrier reification, not an inferred polynomial length. -/
theorem selectedMedianDecision_tapeLength (A : Paper2.SelectedTape.Algorithm)
    (n : ℕ) :
    (selectedMedianDecision A).tapeLength n =
      (Paper2.Unit4Shell.Amplification.reps * (selectedEstimator A).cR) *
        (n + 1) ^ (selectedEstimator A).dR := by
  change Paper2.Unit4Shell.Amplification.reps *
      ((selectedEstimator A).cR * (n + 1) ^ (selectedEstimator A).dR) = _
  ring

theorem selectedMedianDecision_yes (A : Paper2.SelectedTape.Algorithm) (a : ℝ)
    (hA : ∀ w c, Paper2.AModel.targetD w = some c →
      2 / 3 ≤ A.prob w (fun out => ∃ v,
        Paper2.AModel.decodeDyadic out = some v ∧ |v - c| ≤ a))
    (rest : List Bool) (c B k : ℕ)
    (htarget : Paper2.AModel.targetD rest = some c)
    (hk : 2 * a < k) (hcB : c ≤ B) :
    99 / 100 ≤ (selectedMedianDecision A).prob (natField (2 * B + k) ++ rest)
      (· = [true]) := by
  exact Paper2.CmpOwner.medAlgC_yes_natField
    ((selectedEstimator A).toPrefix) rest c a B k hk
    (selectedEstimator_estimatesD A a hA _ rest c htarget) hcB

theorem selectedMedianDecision_no (A : Paper2.SelectedTape.Algorithm) (a : ℝ)
    (hA : ∀ w c, Paper2.AModel.targetD w = some c →
      2 / 3 ≤ A.prob w (fun out => ∃ v,
        Paper2.AModel.decodeDyadic out = some v ∧ |v - c| ≤ a))
    (rest : List Bool) (c B k : ℕ)
    (htarget : Paper2.AModel.targetD rest = some c)
    (hk : 2 * a < k) (hBc : B + k ≤ c) :
    (selectedMedianDecision A).prob (natField (2 * B + k) ++ rest)
      (· = [true]) ≤ 1 / 100 := by
  exact Paper2.CmpOwner.medAlgC_no_natField
    ((selectedEstimator A).toPrefix) rest c a B k hk
    (selectedEstimator_estimatesD A a hA _ rest c htarget) hBc

theorem selectedMedianDecision_polynomial (A : Paper2.SelectedTape.Algorithm) :
    (selectedMedianDecision A).Polynomial :=
  Paper2.CmpOwner.medAlgC_polynomial ((selectedEstimator A).toPrefix)
    (selectedEstimator_toPrefix_polynomial A)

#print axioms selectedMedianDecision_yes
#print axioms selectedMedianDecision_no
#print axioms selectedMedianDecision_polynomial
#print axioms selectedMedianDecision_tapeLength

end Paper2.HeaderStrip
