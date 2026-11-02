import CurrentAdditive.V39HalfMidpoint

/-!
Reusable fixed-rational classifier. The algorithm is independent of the
target value, requested error and matrix size. Accuracy is a local hypothesis
at the supplied input word. This reuses exactly the existing comparisonSpec
and medAlgJudge physical machine, with no second majority implementation.
-/

noncomputable section
open Classical

namespace CurrentAdditive.V39GeneralHalfMajority

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.V39HalfMidpoint
open CurrentAdditive.ModelEndpointReview.RationalEndpoint
open Paper2
open Paper2.AModel (PrefixAlgorithm)

structure GeneralEstimator where
  estimator : SelectedTape.Algorithm
  value : List Bool → ℝ
  comparator : HalfComparator value

private def GeneralEstimator.header (E : GeneralEstimator) : PrefixAlgorithm :=
  (HeaderStrip.selectedEstimator E.estimator).toPrefix

private theorem GeneralEstimator.headerPoly (E : GeneralEstimator) : E.header.Polynomial :=
  HeaderStrip.selectedEstimator_toPrefix_polynomial E.estimator

/-- The same composed comparison adapter and fixed 147-run machine as the
minimal Yao interface. Its clock covers every output, including inaccurate
ones, before the local numerical success hypothesis is used. -/
def GeneralEstimator.majority (E : GeneralEstimator) : PrefixAlgorithm :=
  medAlgJudge E.header _ E.comparator.judge _
    (comparisonSpec E.header E.headerPoly E.comparator)

theorem GeneralEstimator.majority_poly (E : GeneralEstimator) : E.majority.Polynomial :=
  medAlgJudge_polynomial _ _ _ _
    (comparisonSpec E.header E.headerPoly E.comparator) E.headerPoly
    (compareClock_poly E.header E.headerPoly E.comparator)

theorem GeneralEstimator.majority_tape (E : GeneralEstimator) (n : ℕ) :
    E.majority.tapeLength n =
      (147 * (HeaderStrip.selectedEstimator E.estimator).cR) *
        (n + 1) ^ (HeaderStrip.selectedEstimator E.estimator).dR := by
  change 147 * ((HeaderStrip.selectedEstimator E.estimator).cR *
    (n + 1) ^ (HeaderStrip.selectedEstimator E.estimator).dR) = _
  ring

private theorem GeneralEstimator.shape (E : GeneralEstimator) :
    ∃ c d : ℕ, ∀ n, E.majority.tapeLength n = c * (n + 1) ^ d :=
  ⟨147 * (HeaderStrip.selectedEstimator E.estimator).cR,
    (HeaderStrip.selectedEstimator E.estimator).dR, E.majority_tape⟩

def GeneralEstimator.classifier (E : GeneralEstimator) : SelectedTape.Algorithm :=
  SelectedTape.Algorithm.ofPrefixMonomial E.majority E.majority_poly E.shape

theorem GeneralEstimator.classifier_prob (E : GeneralEstimator)
    (word : List Bool) (P : List Bool → Prop) :
    E.classifier.prob word P = E.majority.prob word P :=
  SelectedTape.Algorithm.ofPrefixMonomial_prob E.majority E.majority_poly E.shape word P

/-- A single classifier, independent of D,B,k,u, compares each independent
numerical output to exactly B+k/2. No output-to-output comparison is used.
The local success law may have an input-dependent error radius. -/
theorem GeneralEstimator.fixed_midpoint_law (E : GeneralEstimator)
    (word : List Bool) (D B k : ℕ) (u : ℝ) (_hu : 0 ≤ u)
    (hgap : 2 * u < (k : ℝ))
    (haccurate : 2 / 3 ≤ E.estimator.prob word
      (fun out => |E.value out - (D : ℝ)| ≤ u)) :
    (D ≤ B →
      99 / 100 ≤ E.classifier.prob (natField (2 * B + k) ++ word) (· = [true])) ∧
    (B + k ≤ D →
      E.classifier.prob (natField (2 * B + k) ++ word) (· = [true]) ≤ 1 / 100) := by
  let w := natField (2 * B + k) ++ word
  have hj : ∀ out, E.comparator.judge w out =
      decide (MedianOwner.Below (fun out => some (E.value out))
        ((B : ℝ) + (k : ℝ) / 2) out) := by
    intro out
    have h := E.comparator.judge_header (2 * B + k) word out
    have hm : ((2 * B + k : ℕ) : ℝ) / 2 = (B : ℝ) + (k : ℝ) / 2 := by
      push_cast
      ring
    rw [hm] at h
    simpa [w, MedianOwner.Below] using h
  have ha : 2 / 3 ≤ E.header.prob w
      (fun out => ∃ v, some (E.value out) = some v ∧ |v - (D : ℝ)| ≤ u) := by
    change 2 / 3 ≤ (HeaderStrip.selectedEstimator E.estimator).toPrefix.prob
      (natField (2 * B + k) ++ word) _
    rw [HeaderStrip.selectedEstimator_toPrefix_prob]
    simpa using haccurate
  constructor
  · intro hD
    rw [E.classifier_prob]
    exact medAlgJudge_yes _ _ _ _ _ (fun out => some (E.value out))
      w D u B k hgap hj ha hD
  · intro hD
    rw [E.classifier_prob]
    exact medAlgJudge_no _ _ _ _ _ (fun out => some (E.value out))
      w D u B k hgap hj ha hD

#print axioms GeneralEstimator.majority_poly
#print axioms GeneralEstimator.majority_tape
#print axioms GeneralEstimator.fixed_midpoint_law

end CurrentAdditive.V39GeneralHalfMajority
