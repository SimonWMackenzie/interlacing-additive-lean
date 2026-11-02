import CurrentAdditive.SmallBiasSourceOutputPullback
import Paper2.YaoT26Size

/-!
# Source pullback through the inherited physical clone machine

The inherited source/clone bit machine already emits the Option-B encoding
of the cloned hypergraph. Thus a physical table printer can take that code,
decode it, choose the public parameters, and print the canonical instance.
Only this last, fixed transformation needs a new bit-machine clock.
-/

noncomputable section

namespace CurrentAdditive.SmallBias

open Paper2.YaoX05Draft Paper2.YaoCloneSource Paper2.YaoSourceCodec
open Paper2.YaoBppDraft
open CurrentAdditive.FiniteFieldConstructor
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

def canonicalOfClone (g : ℕ) (source : YaoSource (v27GapParameter g)) : Instance :=
  let t := v27GapParameter g
  let b := exactAddressBits source.2.1
  CanonicalTable.instanceOfTable b t (publicFieldDegree b t)
    ((TrialSearch.firstPassing (publicFieldDegree b t)).getD 0)
    (exactAddress_capacity source.2.1) source.2.2

theorem sourceCanonicalInstance_eq_canonicalOfClone (g : ℕ)
    (G : GLSourceDraft (v27GapParameter g)) (input : List Bool) :
    sourceCanonicalInstance g G input =
      canonicalOfClone g
        (cloneSource (v27GapParameter g)
          (forbiddenColours (v27GapParameter g)) (G.output input)) := by
  rfl

def renderClone (g : ℕ) (bits : List Bool) : List Bool :=
  match decodeAll (v27GapParameter g) bits with
  | some source => encodeInstance (canonicalOfClone g source)
  | none => []

theorem renderClone_source (g : ℕ)
    (G : GLSourceDraft (v27GapParameter g)) (input : List Bool) :
    renderClone g
      (encode (cloneSource (v27GapParameter g)
        (forbiddenColours (v27GapParameter g)) (G.output input))) =
      encodeInstance (sourceCanonicalInstance g G input) := by
  simp [renderClone, decodeAll_encode,
    sourceCanonicalInstance_eq_canonicalOfClone]

theorem source_encoded_polytime_of_clone_renderer (g : ℕ)
    (G : GLSourceDraft (v27GapParameter g))
    (hrender : BitMachine.Polytime (renderClone g)) :
    BitMachine.Polytime (fun input =>
      encodeInstance (sourceCanonicalInstance g G input)) := by
  have h := BitMachineComposition.polytime_comp
    (Paper2.YaoT26Size.draft_yao_source_polytime G) hrender
  simpa only [Function.comp_def, renderClone_source] using h

theorem clone_renderer_np_subset_bpp_fixed_error
    (GF : (t : ℕ) → GLSourceDraft t)
    (L3 : EncodedComplexity.BinaryLanguage)
    (hL : ∀ t, (GF t).L = L3)
    (hard : EncodedComplexity.NPHard L3)
    (u : ℝ) (hu : 0 ≤ u)
    (E : Paper2.SelectedTape.Algorithm) (μ : YaoMeasure)
    (hE : Paper2.YaoSelected.EstimatesYao E μ u)
    (hrender : BitMachine.Polytime (renderClone (sourceEstimatorGap u))) :
    ∀ L, EncodedComplexity.InNP L → Paper2.SelectedTape.InBPP L := by
  exact encoded_printer_np_subset_bpp_fixed_error GF L3 hL hard u hu E μ hE
    (source_encoded_polytime_of_clone_renderer (sourceEstimatorGap u)
      (GF (v27GapParameter (sourceEstimatorGap u))) hrender)

theorem clone_renderer_p_equals_np_fixed_error
    (GF : (t : ℕ) → GLSourceDraft t)
    (L3 : EncodedComplexity.BinaryLanguage)
    (hL : ∀ t, (GF t).L = L3)
    (hard : EncodedComplexity.NPHard L3)
    (u : ℝ) (hu : 0 ≤ u)
    (est : List Bool → List Bool) (hest : BitMachine.Polytime est)
    (μ : YaoMeasure) (hacc : DeterministicEstimatesYao est μ u)
    (hrender : BitMachine.Polytime (renderClone (sourceEstimatorGap u))) :
    PEqualsNP := by
  exact encoded_printer_p_equals_np_fixed_error GF L3 hL hard u hu
    est hest μ hacc
    (source_encoded_polytime_of_clone_renderer (sourceEstimatorGap u)
      (GF (v27GapParameter (sourceEstimatorGap u))) hrender)

#print axioms CurrentAdditive.SmallBias.source_encoded_polytime_of_clone_renderer
#print axioms CurrentAdditive.SmallBias.clone_renderer_np_subset_bpp_fixed_error
#print axioms CurrentAdditive.SmallBias.clone_renderer_p_equals_np_fixed_error

end CurrentAdditive.SmallBias
