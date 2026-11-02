import CurrentAdditive.SmallBiasSourceInstance
import Paper2.YaoSelectedClassifier

/-!
# The selected-tape estimator separates the source promises

Source: v27 `yao:bpp`, using the fixed encoded printed matrix of
`yao:main`. This proves the classifier law on the explicit source output.
The composition of the deterministic source printer with the classifier
is a separate machine theorem, because the full-selector printer clock is
still being constructed.
-/

noncomputable section

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoBppDraft
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

def sourceEstimatorWord (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (input : List Bool) : List Bool :=
  let i := sourcePrintedInstance g G input
  Paper2.AModel.matrixWord i.rows i.cols i.table

def sourceClassifierWord (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (input : List Bool) : List Bool :=
  let i := sourcePrintedInstance g G input
  natField (2 * i.threshold + (g - 1)) ++ sourceEstimatorWord g G input

theorem source_classifier_law (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (E : Paper2.SelectedTape.Algorithm) (μ : YaoMeasure)
    (u : ℝ) (hu : 0 ≤ u) (hg : 2 * u + 3 < (g : ℝ))
    (hE : Paper2.YaoSelected.EstimatesYao E μ u)
    (input : List Bool) :
    (input ∈ G.L →
      99 / 100 ≤ (Paper2.HeaderStrip.selectedClassifier E).prob
        (sourceClassifierWord g G input) (· = [true])) ∧
    (input ∉ G.L →
      (Paper2.HeaderStrip.selectedClassifier E).prob
        (sourceClassifierWord g G input) (· = [true]) ≤ 1 / 100) := by
  let i := sourcePrintedInstance g G input
  have hi : i.Valid := sourcePrintedInstance_valid g G input
  have hgap := sourcePrintedInstance_yes_no g G input
  have hthreshold : i.threshold =
      2 * sourceAddressWidth g G input + 4 * v27GapParameter g + 2 := rfl
  constructor
  · intro hm
    have hD : Dalt .alice
        (ProtocolVerifier.tableGame i.rows i.cols i.table) ≤ i.threshold := by
      rw [hthreshold]
      exact hgap.1 hm
    change 99 / 100 ≤ (Paper2.HeaderStrip.selectedClassifier E).prob
      (natField (2 * i.threshold + (g - 1)) ++
        Paper2.AModel.matrixWord i.rows i.cols i.table) (· = [true])
    exact Paper2.YaoSelected.classifier_yes_instance E μ u hu g hg hE i hi hD
  · intro hn
    have hD : i.threshold + g ≤ Dalt .alice
        (ProtocolVerifier.tableGame i.rows i.cols i.table) := by
      rw [hthreshold]
      exact hgap.2 hn
    change (Paper2.HeaderStrip.selectedClassifier E).prob
      (natField (2 * i.threshold + (g - 1)) ++
        Paper2.AModel.matrixWord i.rows i.cols i.table) (· = [true]) ≤ 1 / 100
    exact Paper2.YaoSelected.classifier_no_instance E μ u hu g hg hE i hi hD

#print axioms CurrentAdditive.SmallBias.source_classifier_law

end CurrentAdditive.SmallBias
