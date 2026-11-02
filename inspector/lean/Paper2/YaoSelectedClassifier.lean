import Paper2.HeaderClassifierSelected
import Paper2.AModelEstimator
import Paper2.YaoBppDraft

/-!
The Yao midpoint law on one supplied encoded matrix instance, in the
source-faithful selected-pair random-tape model.  The estimator sees the
matrix word only.  This module does not assemble the instance from a source
input or identify the resulting algorithm with an NP/BPP endpoint.
-/

noncomputable section

namespace Paper2.YaoSelected

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open Paper2.YaoBppDraft
open Paper2.Yao

/-- D-Y3 estimator success on every decodable matrix word, in the selected
fixed-monomial random-tape model. -/
def EstimatesYao (A : Paper2.SelectedTape.Algorithm) (μ : YaoMeasure)
    (u : ℝ) : Prop :=
  ∀ w c, Paper2.AModel.targetYao μ w = some c →
    2 / 3 ≤ A.prob w (fun out => ∃ v,
      Paper2.AModel.decodeDyadic out = some v ∧ |v - c| ≤ u)

private theorem gap_nat (u : ℝ) (hu : 0 ≤ u) (g : ℕ)
    (hg : 2 * u + 3 < (g : ℝ)) : 3 ≤ g := by
  have h : (3 : ℝ) ≤ g := by linarith
  exact_mod_cast h

private theorem gap_mid (u : ℝ) (hu : 0 ≤ u) (g : ℕ)
    (hg : 2 * u + 3 < (g : ℝ)) : 2 * u < ((g - 3 : ℕ) : ℝ) := by
  rw [Nat.cast_sub (gap_nat u hu g hg)]
  push_cast
  linarith

private theorem header_eq (u : ℝ) (hu : 0 ≤ u) (g B : ℕ)
    (hg : 2 * u + 3 < (g : ℝ)) :
    2 * B + (g - 1) = 2 * (B + 1) + (g - 3) := by
  have hg3 := gap_nat u hu g hg
  omega

/-- Exact D-Y3 success law after the physical strip and uniform-prefix
pullback, on any threshold-prefixed matrix word. -/
theorem estimates_on_header (A : Paper2.SelectedTape.Algorithm)
    (μ : YaoMeasure) (u : ℝ) (hA : EstimatesYao A μ u)
    (n : ℕ) (rest : List Bool) (c : ℕ)
    (htarget : Paper2.AModel.targetYao μ rest = some c) :
    2 / 3 ≤ (Paper2.HeaderStrip.selectedEstimator A).toPrefix.prob
      (natField n ++ rest)
      (fun out => ∃ v, Paper2.AModel.decodeDyadic out = some v ∧ |v - c| ≤ u) := by
  rw [Paper2.HeaderStrip.selectedEstimator_toPrefix_prob]
  exact hA rest c htarget

/-- On a supplied header `2B+g-1`, a Yao target at most `B+1` is
accepted with amplified probability.  This implementation's midpoint
`B+1+(g-3)/2` is exactly the comparator's header midpoint. -/
theorem classifier_yes (A : Paper2.SelectedTape.Algorithm)
    (μ : YaoMeasure) (u : ℝ) (hu : 0 ≤ u) (g : ℕ)
    (hg : 2 * u + 3 < (g : ℝ)) (hA : EstimatesYao A μ u)
    (rest : List Bool) (c B : ℕ)
    (htarget : Paper2.AModel.targetYao μ rest = some c)
    (hcB : c ≤ B + 1) :
    99 / 100 ≤ (Paper2.HeaderStrip.selectedClassifier A).prob
      (natField (2 * B + (g - 1)) ++ rest) (· = [true]) := by
  rw [Paper2.HeaderStrip.selectedClassifier_prob, header_eq u hu g B hg]
  exact Paper2.CmpOwner.medAlgC_yes_natField
    ((Paper2.HeaderStrip.selectedEstimator A).toPrefix) rest c u (B + 1) (g - 3)
    (gap_mid u hu g hg)
    (estimates_on_header A μ u hA _ rest c htarget) hcB

/-- On the same supplied header, a Yao target at least `B+g-2` is
accepted with probability at most `1/100`. -/
theorem classifier_no (A : Paper2.SelectedTape.Algorithm)
    (μ : YaoMeasure) (u : ℝ) (hu : 0 ≤ u) (g : ℕ)
    (hg : 2 * u + 3 < (g : ℝ)) (hA : EstimatesYao A μ u)
    (rest : List Bool) (c B : ℕ)
    (htarget : Paper2.AModel.targetYao μ rest = some c)
    (hBc : B + g - 2 ≤ c) :
    (Paper2.HeaderStrip.selectedClassifier A).prob
      (natField (2 * B + (g - 1)) ++ rest) (· = [true]) ≤ 1 / 100 := by
  have hk : B + 1 + (g - 3) ≤ c := by
    have hg3 := gap_nat u hu g hg
    omega
  rw [Paper2.HeaderStrip.selectedClassifier_prob, header_eq u hu g B hg]
  exact Paper2.CmpOwner.medAlgC_no_natField
    ((Paper2.HeaderStrip.selectedEstimator A).toPrefix) rest c u (B + 1) (g - 3)
    (gap_mid u hu g hg)
    (estimates_on_header A μ u hA _ rest c htarget) hk

/-- D-Y3's matrix word has precisely the target of the corresponding valid
encoded instance. -/
theorem target_matrix (μ : YaoMeasure) (i : Instance) (hi : i.Valid) :
    Paper2.AModel.targetYao μ
      (Paper2.AModel.matrixWord i.rows i.cols i.table) = some (μ.eval i) := by
  calc
    Paper2.AModel.targetYao μ (Paper2.AModel.matrixWord i.rows i.cols i.table) =
        yaoTarget μ (encodeInstance i) := by
          simpa [Paper2.AModel.instanceMatrixWord] using
            Paper2.AModel.targetYao_instance μ (decode_encode i hi)
    _ = some (μ.eval i) := by simp [yaoTarget, decode_encode i hi]

/-- The admitted measure comparison turns the YES bound for `D_A` into
the Yao classifier's `B+1` premise. -/
theorem classifier_yes_instance (A : Paper2.SelectedTape.Algorithm)
    (μ : YaoMeasure) (u : ℝ) (hu : 0 ≤ u) (g : ℕ)
    (hg : 2 * u + 3 < (g : ℝ)) (hA : EstimatesYao A μ u)
    (i : Instance) (hi : i.Valid)
    (hD : Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table) ≤
      i.threshold) :
    99 / 100 ≤ (Paper2.HeaderStrip.selectedClassifier A).prob
      (natField (2 * i.threshold + (g - 1)) ++
        Paper2.AModel.matrixWord i.rows i.cols i.table) (· = [true]) := by
  have hc : μ.eval i ≤ i.threshold + 1 := by
    have hw := (measure_window μ i).2
    omega
  exact classifier_yes A μ u hu g hg hA _ _ _ (target_matrix μ i hi) hc

/-- The admitted measure comparison turns the NO bound for `D_A` into
the Yao classifier's `B+g-2` premise. -/
theorem classifier_no_instance (A : Paper2.SelectedTape.Algorithm)
    (μ : YaoMeasure) (u : ℝ) (hu : 0 ≤ u) (g : ℕ)
    (hg : 2 * u + 3 < (g : ℝ)) (hA : EstimatesYao A μ u)
    (i : Instance) (hi : i.Valid)
    (hD : i.threshold + g ≤
      Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table)) :
    (Paper2.HeaderStrip.selectedClassifier A).prob
      (natField (2 * i.threshold + (g - 1)) ++
        Paper2.AModel.matrixWord i.rows i.cols i.table) (· = [true]) ≤ 1 / 100 := by
  have hc : i.threshold + g - 2 ≤ μ.eval i := by
    have hw := (measure_window μ i).1
    omega
  exact classifier_no A μ u hu g hg hA _ _ _ (target_matrix μ i hi) hc

end Paper2.YaoSelected

#print axioms Paper2.YaoSelected.classifier_yes_instance
#print axioms Paper2.YaoSelected.classifier_no_instance
