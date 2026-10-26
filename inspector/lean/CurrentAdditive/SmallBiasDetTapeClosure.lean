import CurrentAdditive.SmallBiasZeroTapePhysical

/-!
# Zero-tape closure of the physical Yao classifier

An always-accurate deterministic estimator satisfies the inherited
selected-tape accuracy contract with probability one. Header stripping,
median repetition, and source pullback preserve zero tape length, so their
physical machine is deterministic on each source input.
-/

noncomputable section

namespace CurrentAdditive.SmallBias

set_option maxHeartbeats 2000000

open Paper2.YaoBppDraft
open EthInapproximability.CurrentPaper

theorem selectedDetEstimator_estimatesYao (est : List Bool → List Bool)
    (hpoly : BitMachine.Polytime est) (μ : YaoMeasure) (u : ℝ)
    (hest : DeterministicEstimatesYao est μ u) :
    Paper2.YaoSelected.EstimatesYao (selectedDetEstimator est hpoly) μ u := by
  intro w c hc
  obtain ⟨v, hv, hacc⟩ := hest w c hc
  rw [selectedDetEstimator_prob]
  have hgood : ∃ v, Paper2.AModel.decodeDyadic (est w) = some v ∧
      |v - (c : ℝ)| ≤ u := ⟨v, hv, hacc⟩
  simp only [if_pos hgood]
  norm_num

theorem selectedDetClassifier_tape_zero (est : List Bool → List Bool)
    (hpoly : BitMachine.Polytime est) (w : List Bool) :
    (Paper2.HeaderStrip.selectedClassifier
      (selectedDetEstimator est hpoly)).tapeLength w = 0 := by
  let E := selectedDetEstimator est hpoly
  have hc : (Paper2.HeaderStrip.selectedEstimator E).cR = 0 := rfl
  rw [Paper2.ADecider4.classifier_tapeLength]
  change (146 + 1) * ((Paper2.HeaderStrip.selectedEstimator E).cR *
    (w.length + 1) ^ (Paper2.HeaderStrip.selectedEstimator E).dR) = 0
  rw [hc]
  simp

theorem canonicalDetClassifier_tape_zero (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (canonicalClassifierWord g G))
    (est : List Bool → List Bool) (hpoly : BitMachine.Polytime est)
    (input : List Bool) :
    (canonicalSelectedDecider g G hprint
      (selectedDetEstimator est hpoly)).tapeLength input = 0 := by
  unfold canonicalSelectedDecider Paper2.SelectedTape.Algorithm.tapeLength
  have hc : (Paper2.HeaderStrip.selectedClassifier
      (selectedDetEstimator est hpoly)).cR = 0 := by
    have h := selectedDetClassifier_tape_zero est hpoly []
    simpa [Paper2.SelectedTape.Algorithm.tapeLength] using h
  simp [Paper2.SelectedTape.pullback, hc]

#print axioms CurrentAdditive.SmallBias.selectedDetEstimator_estimatesYao
#print axioms CurrentAdditive.SmallBias.canonicalDetClassifier_tape_zero

end CurrentAdditive.SmallBias
