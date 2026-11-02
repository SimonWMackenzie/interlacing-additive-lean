import CurrentAdditive.YaoRendererClocked
import CurrentAdditive.SmallBiasClonedOutputPullback

noncomputable section

namespace CurrentAdditive.SmallBias

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity
open Paper2.YaoX05Draft Paper2.YaoCloneSource Paper2.YaoSourceCodec
open Paper2.YaoBppDraft
open CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

theorem rendererWord_eq_canonicalOfClone (g : ℕ)
    (source : YaoSource (v27GapParameter g)) :
    rendererWord source = encodeInstance (canonicalOfClone g source) := by
  rfl

/-- The clocked physical printer agrees with the exact `renderClone` interface
on every word accepted by the canonical source decoder. -/
theorem physical_renderClone_on_accepted (g : ℕ) :
    ∃ f : List Bool → List Bool,
      BitMachine.Polytime f ∧
      ∀ bits source,
        decodeAll (v27GapParameter g) bits = some source →
        f bits = renderClone g bits := by
  obtain ⟨f, hf, hvalid⟩ := renderer_clocked_polytime
    (v27GapParameter g) (v27GapParameter_ge_four g)
  refine ⟨f, hf, ?_⟩
  intro bits source hdecode
  have hbits : bits = encode source :=
    (decodeAll_eq_some_iff bits source).mp hdecode
  subst bits
  simp only [renderClone, decodeAll_encode]
  exact (hvalid source).trans (rendererWord_eq_canonicalOfClone g source)

theorem physical_source_encoded_polytime (g : ℕ)
    (G : GLSourceDraft (v27GapParameter g)) :
    BitMachine.Polytime (fun input =>
      encodeInstance (sourceCanonicalInstance g G input)) := by
  obtain ⟨f, hf, hsource⟩ := renderer_clocked_polytime
    (v27GapParameter g) (v27GapParameter_ge_four g)
  have hcompose := BitMachineComposition.polytime_comp
    (Paper2.YaoT26Size.draft_yao_source_polytime G) hf
  have heq :
      (f ∘ fun input => encode
        (cloneSource (v27GapParameter g)
          (forbiddenColours (v27GapParameter g)) (G.output input))) =
      (fun input => encodeInstance (sourceCanonicalInstance g G input)) := by
    funext input
    change f (encode (cloneSource (v27GapParameter g)
      (forbiddenColours (v27GapParameter g)) (G.output input))) = _
    rw [hsource]
    rw [rendererWord_eq_canonicalOfClone]
    exact congrArg encodeInstance
      (sourceCanonicalInstance_eq_canonicalOfClone g G input).symm
  rw [← heq]
  exact hcompose

theorem physical_np_subset_bpp_fixed_error
    (GF : (t : ℕ) → GLSourceDraft t)
    (L3 : BinaryLanguage)
    (hL : ∀ t, (GF t).L = L3)
    (hard : NPHard L3)
    (u : ℝ) (hu : 0 ≤ u)
    (E : Paper2.SelectedTape.Algorithm) (μ : YaoMeasure)
    (hE : Paper2.YaoSelected.EstimatesYao E μ u) :
    ∀ L, InNP L → Paper2.SelectedTape.InBPP L := by
  exact encoded_printer_np_subset_bpp_fixed_error GF L3 hL hard
    u hu E μ hE
    (physical_source_encoded_polytime (sourceEstimatorGap u)
      (GF (v27GapParameter (sourceEstimatorGap u))))

theorem physical_p_equals_np_fixed_error
    (GF : (t : ℕ) → GLSourceDraft t)
    (L3 : BinaryLanguage)
    (hL : ∀ t, (GF t).L = L3)
    (hard : NPHard L3)
    (u : ℝ) (hu : 0 ≤ u)
    (est : List Bool → List Bool) (hest : BitMachine.Polytime est)
    (μ : YaoMeasure) (hacc : DeterministicEstimatesYao est μ u) :
    PEqualsNP := by
  exact encoded_printer_p_equals_np_fixed_error GF L3 hL hard
    u hu est hest μ hacc
    (physical_source_encoded_polytime (sourceEstimatorGap u)
      (GF (v27GapParameter (sourceEstimatorGap u))))

#print axioms physical_source_encoded_polytime
#print axioms physical_renderClone_on_accepted
#print axioms physical_np_subset_bpp_fixed_error
#print axioms physical_p_equals_np_fixed_error

end CurrentAdditive.SmallBias
