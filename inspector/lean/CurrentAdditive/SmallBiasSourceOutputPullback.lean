import CurrentAdditive.SmallBiasEncodedClassEndpoint

/-!
# Pullback from the fixed external source output

The author-adopted GL source contract includes a concrete polynomial-time
machine for its encoded occurrence output. The remaining physical target is
one fixed transformation of that output: decode the occurrence graph, clone
it, choose the source-faithful public parameters, and print the canonical
encoded table. Its machine implementation is a separate obligation.
-/

noncomputable section

namespace CurrentAdditive.SmallBias

open Paper2.YaoX05Draft Paper2.YaoCloneSource
open Paper2.YaoBppDraft
open CurrentAdditive.FiniteFieldConstructor
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

theorem source_draft_output_polytime (t : ℕ) (G : GLSourceDraft t) :
    BitMachine.Polytime (fun input => draftOccEncode (G.output input)) := by
  obtain ⟨c, d, hbound⟩ := G.poly
  refine ⟨G.machine, c, d, ?_⟩
  intro input
  exact BitMachine.outputsWithin_mono G.machine (G.runs input) (hbound input)

def canonicalOfDraft (g : ℕ) (occ : DraftOccSource (v27GapParameter g)) : Instance :=
  let t := v27GapParameter g
  let source := cloneSource t (forbiddenColours t) occ
  let b := exactAddressBits source.2.1
  CanonicalTable.instanceOfTable b t (publicFieldDegree b t)
    ((TrialSearch.firstPassing (publicFieldDegree b t)).getD 0)
    (exactAddress_capacity source.2.1) source.2.2

theorem sourceCanonicalInstance_eq_canonicalOfDraft (g : ℕ)
    (G : GLSourceDraft (v27GapParameter g)) (input : List Bool) :
    sourceCanonicalInstance g G input = canonicalOfDraft g (G.output input) := by
  rfl

def renderDraft (g : ℕ) (bits : List Bool) : List Bool :=
  match draftOccDecode (v27GapParameter g) bits with
  | some (occ, []) => encodeInstance (canonicalOfDraft g occ)
  | _ => []

theorem renderDraft_source (g : ℕ)
    (G : GLSourceDraft (v27GapParameter g)) (input : List Bool) :
    renderDraft g (draftOccEncode (G.output input)) =
      encodeInstance (sourceCanonicalInstance g G input) := by
  have hdec : draftOccDecode (v27GapParameter g)
      (draftOccEncode (G.output input)) = some (G.output input, []) := by
    simpa using draftOccDecode_encode (G.output input) []
  simp [renderDraft, hdec, sourceCanonicalInstance_eq_canonicalOfDraft]

theorem source_encoded_polytime_of_renderer (g : ℕ)
    (G : GLSourceDraft (v27GapParameter g))
    (hrender : BitMachine.Polytime (renderDraft g)) :
    BitMachine.Polytime (fun input =>
      encodeInstance (sourceCanonicalInstance g G input)) := by
  have h := BitMachineComposition.polytime_comp
    (source_draft_output_polytime (v27GapParameter g) G) hrender
  simpa only [Function.comp_def, renderDraft_source] using h

theorem renderer_np_subset_bpp_fixed_error
    (GF : (t : ℕ) → GLSourceDraft t)
    (L3 : EncodedComplexity.BinaryLanguage)
    (hL : ∀ t, (GF t).L = L3)
    (hard : EncodedComplexity.NPHard L3)
    (u : ℝ) (hu : 0 ≤ u)
    (E : Paper2.SelectedTape.Algorithm) (μ : YaoMeasure)
    (hE : Paper2.YaoSelected.EstimatesYao E μ u)
    (hrender : BitMachine.Polytime (renderDraft (sourceEstimatorGap u))) :
    ∀ L, EncodedComplexity.InNP L → Paper2.SelectedTape.InBPP L := by
  exact encoded_printer_np_subset_bpp_fixed_error GF L3 hL hard u hu E μ hE
    (source_encoded_polytime_of_renderer (sourceEstimatorGap u)
      (GF (v27GapParameter (sourceEstimatorGap u))) hrender)

theorem renderer_p_equals_np_fixed_error
    (GF : (t : ℕ) → GLSourceDraft t)
    (L3 : EncodedComplexity.BinaryLanguage)
    (hL : ∀ t, (GF t).L = L3)
    (hard : EncodedComplexity.NPHard L3)
    (u : ℝ) (hu : 0 ≤ u)
    (est : List Bool → List Bool) (hest : BitMachine.Polytime est)
    (μ : YaoMeasure) (hacc : DeterministicEstimatesYao est μ u)
    (hrender : BitMachine.Polytime (renderDraft (sourceEstimatorGap u))) :
    PEqualsNP := by
  exact encoded_printer_p_equals_np_fixed_error GF L3 hL hard u hu
    est hest μ hacc
    (source_encoded_polytime_of_renderer (sourceEstimatorGap u)
      (GF (v27GapParameter (sourceEstimatorGap u))) hrender)

#print axioms CurrentAdditive.SmallBias.source_draft_output_polytime
#print axioms CurrentAdditive.SmallBias.source_encoded_polytime_of_renderer
#print axioms CurrentAdditive.SmallBias.renderer_np_subset_bpp_fixed_error
#print axioms CurrentAdditive.SmallBias.renderer_p_equals_np_fixed_error

end CurrentAdditive.SmallBias
