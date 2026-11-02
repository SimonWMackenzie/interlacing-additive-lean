import CurrentAdditive.V39ApprovedYaoCompiler
import CurrentAdditive.V39MinimalActualEndpoint

/-! Same-table fixed-error hardness from the approved source record.
The encoded-table machine and midpoint-header machine are constructed,
not assumed. External source existence and its language's NP-hardness
remain the contract's explicit boundary. Numerical comparison is required
only at this table's fixed midpoint on its actual estimator outputs. -/

noncomputable section
set_option autoImplicit false
namespace CurrentAdditive.V39ApprovedYaoEndpoint

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity
open CurrentAdditive.YaoMinimalSource
open CurrentAdditive.SmallBias
open CurrentAdditive.V39ActualYaoEndpoint
open CurrentAdditive.V39ApprovedYaoCompiler
open CurrentAdditive.V39YaoEndpointJoin (estimatorParameter estimatorParameter_valid estimatorParameter_gap)
open CurrentAdditive.V39MinimalActualEndpoint (matrixWord midpointNumerator sourceWord sourceDecider sourceDecider_decides)
open Paper2 Paper2.Yao Paper2.YaoBppDraft Paper2.YaoX05Draft

theorem fixed_gap_reduction (k : ℕ) (_hk : 1 ≤ k)
    (G : GLSourceDraft (CurrentAdditive.SmallBias.v37GapParameter k)) :
    ∃ F : List Bool → Instance,
      BitMachine.Polytime (fun input => encodeInstance (F input)) ∧
      (∀ input, (F input).Valid) ∧
      (∀ input,
        (input ∈ G.L → Paper2.Yao.Dalt .alice (ProtocolVerifier.tableGame
          (F input).rows (F input).cols (F input).table) ≤ (F input).threshold) ∧
        (input ∉ G.L → (F input).threshold + k ≤ Paper2.Yao.Dalt .alice
          (ProtocolVerifier.tableGame (F input).rows (F input).cols (F input).table))) := by
  let t := CurrentAdditive.SmallBias.v37GapParameter k
  let F := fun input => V39MinimalActualEndpoint.selectedInstance (ofDraft G) input
  have ht : 4 ≤ t := CurrentAdditive.SmallBias.v37GapParameter_ge_four k
  have hk' : k ≤ 2*t-8 := CurrentAdditive.SmallBias.v37GapParameter_gap k
  refine ⟨F, instanceWord_polytime (ofDraft G) ht,
    selectedInstance_valid (ofDraft G), fun input => ?_⟩
  have h := V39MinimalActualEndpoint.selectedInstance_gap (ofDraft G) ht input
  exact ⟨h.1,fun hn => (Nat.add_le_add_left hk' (F input).threshold).trans (h.2 hn)⟩

theorem sourceWord_polytime {t : ℕ} (G : SourceInput t) (ht : 4 ≤ t)
    (hk : 0 < 2*t-8) : BitMachine.Polytime (sourceWord G) :=
  V39MinimalActualEndpoint.sourceWord_polytime_of_encoded G hk (instanceWord_polytime G ht)

theorem source_decides {t : ℕ} (G : SourceInput t) (ht : 4 ≤ t)
    {μ : YaoMeasure} {u : ℝ} (E : ValidYaoEstimator μ u) (hu : 0 ≤ u)
    (hgap : 2*(u+2) < ((2*t-8 : ℕ) : ℝ))
    (hcompare : ∀ input, E.algorithm.actualComparison
      (matrixWord G input) (midpointNumerator G input)) :
    SelectedTape.InBPP G.L := by
  have hk : 0 < 2*t-8 := by
    have h : (0 : ℝ) < ((2*t-8 : ℕ) : ℝ) := by linarith
    exact_mod_cast h
  let hp := sourceWord_polytime G ht hk
  exact ⟨sourceDecider G E hp, sourceDecider_decides G ht E hu hgap hp hcompare⟩

theorem source_inP {t : ℕ} (G : SourceInput t) (ht : 4 ≤ t)
    {μ : YaoMeasure} {u : ℝ} (E : ValidYaoEstimator μ u) (hu : 0 ≤ u)
    (hz : E.algorithm.estimator.cR = 0)
    (hgap : 2*(u+2) < ((2*t-8 : ℕ) : ℝ))
    (hcompare : ∀ input, E.algorithm.actualComparison
      (matrixWord G input) (midpointNumerator G input)) :
    ComplexityReductionClosure.InP G.L := by
  have hk : 0 < 2*t-8 := by
    have h : (0 : ℝ) < ((2*t-8 : ℕ) : ℝ) := by linarith
    exact_mod_cast h
  let hp := sourceWord_polytime G ht hk
  exact actual_inP_of_decides E.algorithm hz (sourceWord G) hp G.L
    (sourceDecider_decides G ht E hu hgap hp hcompare)

theorem fixed_error_np_subset_bpp (u : ℝ) (hu : 0 ≤ u)
    (G : GLSourceDraft (estimatorParameter u)) (hard : NPHard G.L)
    {μ : YaoMeasure} (E : ValidYaoEstimator μ u)
    (hcompare : ∀ input, E.algorithm.actualComparison
      (matrixWord (ofDraft G) input) (midpointNumerator (ofDraft G) input)) :
    ∀ L, InNP L → SelectedTape.InBPP L :=
  SelectedTape.np_subset_inBPP hard
    (source_decides (ofDraft G) (estimatorParameter_valid u) E hu
      (estimatorParameter_gap u) hcompare)

theorem fixed_error_p_equals_np (u : ℝ) (hu : 0 ≤ u)
    (G : GLSourceDraft (estimatorParameter u)) (hard : NPHard G.L)
    {μ : YaoMeasure} (E : ValidYaoEstimator μ u)
    (hz : E.algorithm.estimator.cR = 0)
    (hcompare : ∀ input, E.algorithm.actualComparison
      (matrixWord (ofDraft G) input) (midpointNumerator (ofDraft G) input)) :
    PEqualsNP :=
  p_equals_np_of_np_subset_p
    (ComplexityReductionClosure.npHard_inP_implies_np_subset_p hard
      (source_inP (ofDraft G) (estimatorParameter_valid u) E hu hz
        (estimatorParameter_gap u) hcompare))

/- The shared-language version keeps the external source-family and the
visible NP-hardness premise separate, as in the approved source boundary. -/
theorem fixed_error_np_subset_bpp_of_family (u : ℝ) (hu : 0 ≤ u)
    (GF : (t : ℕ) → GLSourceDraft t) (L3 : BinaryLanguage)
    (hL : ∀ t, (GF t).L = L3) (hard : NPHard L3)
    {μ : YaoMeasure} (E : ValidYaoEstimator μ u)
    (hcompare : ∀ input, E.algorithm.actualComparison
      (matrixWord (ofDraft (GF (estimatorParameter u))) input)
      (midpointNumerator (ofDraft (GF (estimatorParameter u))) input)) :
    ∀ L, InNP L → SelectedTape.InBPP L :=
  fixed_error_np_subset_bpp u hu (GF (estimatorParameter u))
    (by simpa only [hL] using hard) E hcompare

theorem fixed_error_p_equals_np_of_family (u : ℝ) (hu : 0 ≤ u)
    (GF : (t : ℕ) → GLSourceDraft t) (L3 : BinaryLanguage)
    (hL : ∀ t, (GF t).L = L3) (hard : NPHard L3)
    {μ : YaoMeasure} (E : ValidYaoEstimator μ u)
    (hz : E.algorithm.estimator.cR = 0)
    (hcompare : ∀ input, E.algorithm.actualComparison
      (matrixWord (ofDraft (GF (estimatorParameter u))) input)
      (midpointNumerator (ofDraft (GF (estimatorParameter u))) input)) :
    PEqualsNP :=
  fixed_error_p_equals_np u hu (GF (estimatorParameter u))
    (by simpa only [hL] using hard) E hz hcompare

#print axioms sourceWord_polytime
#print axioms fixed_gap_reduction
#print axioms source_decides
#print axioms source_inP
#print axioms fixed_error_np_subset_bpp
#print axioms fixed_error_p_equals_np
#print axioms fixed_error_np_subset_bpp_of_family
#print axioms fixed_error_p_equals_np_of_family
end CurrentAdditive.V39ApprovedYaoEndpoint
