import CurrentAdditive.SmallBiasSourceClassifier
import Paper2.BindSelected

/-!
# Conditional randomized class endpoint for the fixed printed word

Source: v27 `yao:bpp`. The semantic source/classifier law and the
selected-tape pullback are proved. The sole additional machine premise
here is `BitMachine.Polytime` for the particular source-to-headered-word
function defined in `SmallBiasSourceClassifier`. The canonical physical
printer may require a row-reindexing bridge before discharging it.
-/

noncomputable section

namespace CurrentAdditive.SmallBias

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity
open Paper2.YaoBppDraft

def sourceSelectedDecider (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (sourceClassifierWord g G))
    (E : Paper2.SelectedTape.Algorithm) : Paper2.SelectedTape.Algorithm :=
  Paper2.SelectedTape.pullback (sourceClassifierWord g G) hprint
    (Paper2.HeaderStrip.selectedClassifier E)

theorem sourceSelectedDecider_decides (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (sourceClassifierWord g G))
    (E : Paper2.SelectedTape.Algorithm) (μ : YaoMeasure)
    (u : ℝ) (hu : 0 ≤ u) (hg : 2 * u + 3 < (g : ℝ))
    (hE : Paper2.YaoSelected.EstimatesYao E μ u) :
    (sourceSelectedDecider g G hprint E).Decides G.L (1 / 3) := by
  intro input
  have h := source_classifier_law g G E μ u hu hg hE input
  constructor
  · intro hm
    rw [sourceSelectedDecider, Paper2.SelectedTape.pullback_prob]
    have hyes := h.1 hm
    linarith
  · intro hn
    rw [sourceSelectedDecider, Paper2.SelectedTape.pullback_prob]
    have hno := h.2 hn
    linarith

theorem source_inBPP (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (sourceClassifierWord g G))
    (E : Paper2.SelectedTape.Algorithm) (μ : YaoMeasure)
    (u : ℝ) (hu : 0 ≤ u) (hg : 2 * u + 3 < (g : ℝ))
    (hE : Paper2.YaoSelected.EstimatesYao E μ u) :
    Paper2.SelectedTape.InBPP G.L :=
  ⟨sourceSelectedDecider g G hprint E,
    sourceSelectedDecider_decides g G hprint E μ u hu hg hE⟩

theorem np_subset_bpp_of_printed_estimator (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hard : NPHard G.L)
    (hprint : BitMachine.Polytime (sourceClassifierWord g G))
    (E : Paper2.SelectedTape.Algorithm) (μ : YaoMeasure)
    (u : ℝ) (hu : 0 ≤ u) (hg : 2 * u + 3 < (g : ℝ))
    (hE : Paper2.YaoSelected.EstimatesYao E μ u) :
    ∀ L, InNP L → Paper2.SelectedTape.InBPP L :=
  Paper2.SelectedTape.np_subset_inBPP hard
    (source_inBPP g G hprint E μ u hu hg hE)

/-- For every fixed error `u`, this public integer exceeds the gap needed
by the checked selected-tape midpoint classifier. -/
def sourceEstimatorGap (u : ℝ) : ℕ := ⌈2 * u⌉₊ + 4

theorem sourceEstimatorGap_bound (u : ℝ) :
    2 * u + 3 < (sourceEstimatorGap u : ℝ) := by
  have h := Nat.le_ceil (2 * u)
  unfold sourceEstimatorGap
  push_cast
  linarith

theorem np_subset_bpp_fixed_error
    (GF : (t : ℕ) → Paper2.YaoX05Draft.GLSourceDraft t)
    (L3 : BinaryLanguage) (hL : ∀ t, (GF t).L = L3)
    (hard : NPHard L3)
    (u : ℝ) (hu : 0 ≤ u)
    (E : Paper2.SelectedTape.Algorithm) (μ : YaoMeasure)
    (hE : Paper2.YaoSelected.EstimatesYao E μ u)
    (hprint : BitMachine.Polytime
      (sourceClassifierWord (sourceEstimatorGap u)
        (GF (v27GapParameter (sourceEstimatorGap u))))) :
    ∀ L, InNP L → Paper2.SelectedTape.InBPP L := by
  have hhard : NPHard (GF (v27GapParameter (sourceEstimatorGap u))).L := by
    rw [hL]
    exact hard
  exact np_subset_bpp_of_printed_estimator (sourceEstimatorGap u)
    (GF (v27GapParameter (sourceEstimatorGap u))) hhard hprint E μ u hu
    (sourceEstimatorGap_bound u) hE

#print axioms CurrentAdditive.SmallBias.sourceSelectedDecider_decides
#print axioms CurrentAdditive.SmallBias.np_subset_bpp_fixed_error

end CurrentAdditive.SmallBias
