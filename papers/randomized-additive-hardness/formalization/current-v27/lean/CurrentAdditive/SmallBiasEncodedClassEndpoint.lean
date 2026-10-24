import CurrentAdditive.SmallBiasHeaderPhysical

/-!
# Class endpoints with one exact encoded-printer runtime premise

Source: v27 `yao:bpp` and deterministic clause. The source-faithful table
uses `H=2^clog₂(max(1,|E|))`. Its physical encoded-instance printer is
the sole remaining reduction-machine premise; the header, comparator,
selected randomized closure, deterministic closure, and standard P subset
NP inclusion are proved in the imported modules.
-/

noncomputable section

namespace CurrentAdditive.SmallBias

open Paper2.YaoBppDraft
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity

private theorem fixedGap_gt_one (u : ℝ) : 1 < sourceEstimatorGap u := by
  unfold sourceEstimatorGap
  omega

theorem encoded_printer_np_subset_bpp_fixed_error
    (GF : (t : ℕ) → Paper2.YaoX05Draft.GLSourceDraft t)
    (L3 : BinaryLanguage) (hL : ∀ t, (GF t).L = L3)
    (hard : NPHard L3)
    (u : ℝ) (hu : 0 ≤ u)
    (E : Paper2.SelectedTape.Algorithm) (μ : YaoMeasure)
    (hE : Paper2.YaoSelected.EstimatesYao E μ u)
    (hencoded : BitMachine.Polytime (fun input =>
      encodeInstance (sourceCanonicalInstance (sourceEstimatorGap u)
        (GF (v27GapParameter (sourceEstimatorGap u))) input))) :
    ∀ L, InNP L → Paper2.SelectedTape.InBPP L := by
  have hprint := canonicalClassifierWord_polytime_of_encoded
    (sourceEstimatorGap u) (fixedGap_gt_one u)
    (GF (v27GapParameter (sourceEstimatorGap u))) hencoded
  exact canonical_np_subset_bpp_fixed_error GF L3 hL hard u hu E μ hE hprint

theorem encoded_printer_p_equals_np_fixed_error
    (GF : (t : ℕ) → Paper2.YaoX05Draft.GLSourceDraft t)
    (L3 : BinaryLanguage) (hL : ∀ t, (GF t).L = L3)
    (hard : NPHard L3)
    (u : ℝ) (hu : 0 ≤ u)
    (est : List Bool → List Bool) (hest : BitMachine.Polytime est)
    (μ : YaoMeasure) (hacc : DeterministicEstimatesYao est μ u)
    (hencoded : BitMachine.Polytime (fun input =>
      encodeInstance (sourceCanonicalInstance (sourceEstimatorGap u)
        (GF (v27GapParameter (sourceEstimatorGap u))) input))) :
    PEqualsNP := by
  have hprint := canonicalClassifierWord_polytime_of_encoded
    (sourceEstimatorGap u) (fixedGap_gt_one u)
    (GF (v27GapParameter (sourceEstimatorGap u))) hencoded
  exact physical_canonical_p_equals_np_fixed_error
    GF L3 hL hard u hu est hest μ hacc hprint

#print axioms CurrentAdditive.SmallBias.encoded_printer_np_subset_bpp_fixed_error
#print axioms CurrentAdditive.SmallBias.encoded_printer_p_equals_np_fixed_error

end CurrentAdditive.SmallBias
