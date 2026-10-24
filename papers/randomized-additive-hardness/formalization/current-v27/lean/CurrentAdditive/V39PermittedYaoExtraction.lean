import CurrentAdditive.V39PermittedNumericalExtraction
import CurrentAdditive.V39ApprovedYaoEndpoint

/-! Source-selected endpoints without a residual numerical comparison
assumption. The actual approved source constructor proves both table
validity and the polynomial binary length of its fixed midpoint. -/

noncomputable section
open Classical

namespace CurrentAdditive.V39PermittedYaoExtraction

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity
open CurrentAdditive.V39PermittedNumericalExtraction
open CurrentAdditive.V39ActualYaoEndpoint
open CurrentAdditive.V39ActualOutputMajority
open CurrentAdditive.SmallBias
open CurrentAdditive.V39MinimalActualEndpoint
open CurrentAdditive.YaoMinimalSource
open CurrentAdditive.Eventual (entries entries_matrixWord)
open CurrentAdditive.ModelEndpointReview.RationalEndpoint
open CurrentAdditive.V39YaoEndpointJoin (estimatorParameter)
open Paper2 Paper2.Yao Paper2.YaoBppDraft Paper2.YaoX05Draft

/-- The exact source midpoint, including its sign/tag bit, satisfies a
linear binary-code bound in this same table's number of entries. -/
theorem selected_midpoint_code_length {t : ℕ} (G : SourceInput t)
    (input : List Bool) :
    (rationalCode (midpointNumerator G input : ℤ) 1).length ≤
      (20 * t + 101) * (entries (matrixWord G input) + 1) ^ 1 := by
  have hT : entries (matrixWord G input) =
      (selectedInstance G input).rows * (selectedInstance G input).cols := by
    exact entries_matrixWord _ _ _ (YaoMinimalSource.selectedInstance_valid G input)
  have h := code_length_of_header_bound (midpointNumerator G input)
    ((selectedInstance G input).rows * (selectedInstance G input).cols)
    (20 * t + 100) 1 (by
      simpa only [pow_one] using midpoint_header_length G input)
  simpa only [hT, Nat.add_assoc] using h

def RawAccurate (A : PermittedEstimator) (μ : YaoMeasure) (u : ℝ) : Prop :=
  ∀ word D, AModel.targetYao μ word = some D →
    2 / 3 ≤ A.raw.prob word (fun out => |A.value out - (D : ℝ)| ≤ u)

/-- One physical estimator and one physical comparator satisfy every
selected source-table comparison. All raw event laws and the original
tape schedule are preserved. Accuracy is transported only on valid tables. -/
theorem extract_selected {μ : YaoMeasure} {u : ℝ}
    (A : PermittedEstimator) (haccuracy : RawAccurate A μ u)
    {t : ℕ} (G : SourceInput t) :
    ∃ E : ValidYaoEstimator μ u,
      (∀ input, E.algorithm.actualComparison
        (matrixWord G input) (midpointNumerator G input)) ∧
      E.algorithm.estimator.cR = A.raw.cR := by
  obtain ⟨E, hestimator, hvalue, hcompare, hevent⟩ := extract_family A
    (matrixWord G) (midpointNumerator G) (20 * t + 101) 1
    (fun input => valid_matrix _ (YaoMinimalSource.selectedInstance_valid G input))
    (selected_midpoint_code_length G)
  let V : ValidYaoEstimator μ u := {
    algorithm := E
    accurate := by
      intro word D hD
      rw [hvalue, hevent word (valid_of_target hD)]
      exact haccuracy word D hD }
  refine ⟨V, hcompare, ?_⟩
  change E.estimator.cR = A.raw.cR
  rw [hestimator]
  rfl

/-- Every permitted bounded-error numerical estimator for any of the
four stated alternating costs gives NP contained in BPP. No comparison,
printing, stronger-source or midpoint-length hypothesis remains. -/
theorem permitted_fixed_error_np_subset_bpp (u : ℝ) (hu : 0 ≤ u)
    (G : GLSourceDraft (estimatorParameter u)) (hard : NPHard G.L)
    {μ : YaoMeasure} (A : PermittedEstimator) (haccuracy : RawAccurate A μ u) :
    ∀ L, InNP L → SelectedTape.InBPP L := by
  obtain ⟨E, hcompare, _⟩ := extract_selected A haccuracy (ofDraft G)
  exact V39ApprovedYaoEndpoint.fixed_error_np_subset_bpp u hu G hard E hcompare

/-- The deterministic special case uses exactly zero original random bits;
the same physical endpoint therefore gives P=NP. -/
theorem permitted_fixed_error_p_equals_np (u : ℝ) (hu : 0 ≤ u)
    (G : GLSourceDraft (estimatorParameter u)) (hard : NPHard G.L)
    {μ : YaoMeasure} (A : PermittedEstimator) (haccuracy : RawAccurate A μ u)
    (hz : A.raw.cR = 0) : PEqualsNP := by
  obtain ⟨E, hcompare, htape⟩ := extract_selected A haccuracy (ofDraft G)
  exact V39ApprovedYaoEndpoint.fixed_error_p_equals_np u hu G hard E
    (htape.trans hz) hcompare

#print axioms selected_midpoint_code_length
#print axioms extract_selected
#print axioms permitted_fixed_error_np_subset_bpp
#print axioms permitted_fixed_error_p_equals_np

end CurrentAdditive.V39PermittedYaoExtraction
