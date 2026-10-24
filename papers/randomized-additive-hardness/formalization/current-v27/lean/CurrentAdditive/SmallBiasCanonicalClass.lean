import CurrentAdditive.SmallBiasCanonicalSource
import CurrentAdditive.SmallBiasClassBPP

/-!
# Fixed-error randomized endpoint on the source-faithful canonical table

Source: v27 `yao:bpp`, with the exact least-power-of-two edge bank from
`07-yao.tex`. The classifier law is unconditional relative to the explicit
GL source and estimator contract. The class endpoint additionally requires
the polynomial clock for this exact deterministic source-to-word function.
-/

noncomputable section

namespace CurrentAdditive.SmallBias

set_option maxHeartbeats 2000000

open Paper2.Yao Paper2.YaoBppDraft
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity

def canonicalEstimatorWord (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (input : List Bool) : List Bool :=
  let i := sourceCanonicalInstance g G input
  Paper2.AModel.matrixWord i.rows i.cols i.table

def canonicalClassifierWord (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (input : List Bool) : List Bool :=
  let i := sourceCanonicalInstance g G input
  natField (2 * i.threshold + (g - 1)) ++ canonicalEstimatorWord g G input

theorem canonical_classifier_law (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (E : Paper2.SelectedTape.Algorithm) (μ : YaoMeasure)
    (u : ℝ) (hu : 0 ≤ u) (hg : 2 * u + 3 < (g : ℝ))
    (hE : Paper2.YaoSelected.EstimatesYao E μ u)
    (input : List Bool) :
    (input ∈ G.L →
      99 / 100 ≤ (Paper2.HeaderStrip.selectedClassifier E).prob
        (canonicalClassifierWord g G input) (· = [true])) ∧
    (input ∉ G.L →
      (Paper2.HeaderStrip.selectedClassifier E).prob
        (canonicalClassifierWord g G input) (· = [true]) ≤ 1 / 100) := by
  let i := sourceCanonicalInstance g G input
  have hi : i.Valid := sourceCanonicalInstance_valid g G input
  have hgap := sourceCanonicalInstance_yes_no g G input
  have hthreshold : i.threshold =
      2 * sourceExactAddressWidth g G input + 4 * v27GapParameter g + 2 := rfl
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

def canonicalSelectedDecider (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (canonicalClassifierWord g G))
    (E : Paper2.SelectedTape.Algorithm) : Paper2.SelectedTape.Algorithm :=
  Paper2.SelectedTape.pullback (canonicalClassifierWord g G) hprint
    (Paper2.HeaderStrip.selectedClassifier E)

theorem canonicalSelectedDecider_decides (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (canonicalClassifierWord g G))
    (E : Paper2.SelectedTape.Algorithm) (μ : YaoMeasure)
    (u : ℝ) (hu : 0 ≤ u) (hg : 2 * u + 3 < (g : ℝ))
    (hE : Paper2.YaoSelected.EstimatesYao E μ u) :
    (canonicalSelectedDecider g G hprint E).Decides G.L (1 / 3) := by
  intro input
  have h := canonical_classifier_law g G E μ u hu hg hE input
  constructor
  · intro hm
    rw [canonicalSelectedDecider, Paper2.SelectedTape.pullback_prob]
    have hyes := h.1 hm
    linarith
  · intro hn
    rw [canonicalSelectedDecider, Paper2.SelectedTape.pullback_prob]
    have hno := h.2 hn
    linarith

theorem canonical_np_subset_bpp_fixed_error
    (GF : (t : ℕ) → Paper2.YaoX05Draft.GLSourceDraft t)
    (L3 : BinaryLanguage) (hL : ∀ t, (GF t).L = L3)
    (hard : NPHard L3)
    (u : ℝ) (hu : 0 ≤ u)
    (E : Paper2.SelectedTape.Algorithm) (μ : YaoMeasure)
    (hE : Paper2.YaoSelected.EstimatesYao E μ u)
    (hprint : BitMachine.Polytime
      (canonicalClassifierWord (sourceEstimatorGap u)
        (GF (v27GapParameter (sourceEstimatorGap u))))) :
    ∀ L, InNP L → Paper2.SelectedTape.InBPP L := by
  let g := sourceEstimatorGap u
  let G := GF (v27GapParameter g)
  have hhard : NPHard G.L := by
    rw [hL]
    exact hard
  have hmem : Paper2.SelectedTape.InBPP G.L :=
    ⟨canonicalSelectedDecider g G hprint E,
      canonicalSelectedDecider_decides g G hprint E μ u hu
        (sourceEstimatorGap_bound u) hE⟩
  exact Paper2.SelectedTape.np_subset_inBPP hhard hmem

#print axioms CurrentAdditive.SmallBias.canonical_classifier_law
#print axioms CurrentAdditive.SmallBias.canonical_np_subset_bpp_fixed_error

end CurrentAdditive.SmallBias
