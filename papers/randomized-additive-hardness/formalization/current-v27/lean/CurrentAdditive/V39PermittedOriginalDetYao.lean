import CurrentAdditive.V39PermittedYaoExtraction
import CurrentAdditive.V39PermittedDeterministicExtraction

/-! The deterministic Yao consequence consumes the original deterministic
machine whose input is a matrix word. The zero-tape representation used
internally by the already proved majority endpoint is constructed here;
it is not an extra requirement on the permitted estimator. -/

noncomputable section
open Classical

namespace CurrentAdditive.V39PermittedOriginalDetYao

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity
open CurrentAdditive.V39PermittedNumericalExtraction
open CurrentAdditive.V39PermittedDeterministicExtraction
open CurrentAdditive.V39PermittedYaoExtraction
open CurrentAdditive.V39ActualYaoEndpoint
open CurrentAdditive.V39ActualOutputMajority
open CurrentAdditive.V39MinimalActualEndpoint
open CurrentAdditive.YaoMinimalSource
open CurrentAdditive.V39YaoEndpointJoin (estimatorParameter)
open CurrentAdditive.SmallBias
open Paper2 Paper2.Yao Paper2.YaoBppDraft Paper2.YaoX05Draft

def DeterministicAccurate (A : PermittedDeterministicEstimator)
    (μ : YaoMeasure) (u : ℝ) : Prop :=
  ∀ word D, AModel.targetYao μ word = some D →
    |A.value (A.output word) - (D : ℝ)| ≤ u

/-- Valid-domain deterministic timeout, raw rational-output projection,
and the zero-tape physical wrapper are all constructed. The result keeps
the exact current source's matrix and the proved fixed midpoint. -/
theorem extract_deterministic_selected {μ : YaoMeasure} {u : ℝ}
    (A : PermittedDeterministicEstimator) (haccuracy : DeterministicAccurate A μ u)
    {t : ℕ} (G : SourceInput t) :
    ∃ V : ValidYaoEstimator μ u,
      (∀ input, V.algorithm.actualComparison
        (matrixWord G input) (midpointNumerator G input)) ∧
      V.algorithm.estimator.cR = 0 := by
  obtain ⟨E, hvalue, houtput, hcompare⟩ :=
    V39PermittedDeterministicExtraction.extract_family A
      (matrixWord G) (midpointNumerator G) (20 * t + 101) 1
      (fun input => valid_matrix _ (YaoMinimalSource.selectedInstance_valid G input))
      (selected_midpoint_code_length G)
  let actual : ActualEstimator := {
    estimator := selectedDetEstimator E.output E.physical
    value := E.value
    comparator := E.comparator }
  let V : ValidYaoEstimator μ u := {
    algorithm := actual
    accurate := by
      intro word D hD
      have hgood : |E.value (E.output word) - (D : ℝ)| ≤ u := by
        rw [hvalue, houtput word (valid_of_target hD)]
        exact haccuracy word D hD
      change 2 / 3 ≤ (selectedDetEstimator E.output E.physical).prob word _
      rw [selectedDetEstimator_prob]
      change 2 / 3 ≤ if |E.value (E.output word) - (D : ℝ)| ≤ u then 1 else 0
      rw [if_pos hgood]
      norm_num }
  refine ⟨V, ?_, rfl⟩
  intro input tape
  change E.comparator.output
    (EncodedComplexity.pair (natField (midpointNumerator G input) ++ matrixWord G input)
      ((selectedDetEstimator E.output E.physical).output (matrixWord G input)
        (List.ofFn tape))) = _
  simp only [selectedDetEstimator_output]
  exact hcompare input

/-- Original-input deterministic permitted numerical estimators for each
of the four stated alternating costs imply P=NP. The caller supplies
neither a zero-tape representation nor a residual comparison law. -/
theorem permitted_original_deterministic_p_equals_np (u : ℝ) (hu : 0 ≤ u)
    (G : GLSourceDraft (estimatorParameter u)) (hard : NPHard G.L)
    {μ : YaoMeasure} (A : PermittedDeterministicEstimator)
    (haccuracy : DeterministicAccurate A μ u) : PEqualsNP := by
  obtain ⟨V, hcompare, htape⟩ := extract_deterministic_selected A haccuracy (ofDraft G)
  exact V39ApprovedYaoEndpoint.fixed_error_p_equals_np u hu G hard V htape hcompare

#print axioms extract_deterministic_selected
#print axioms permitted_original_deterministic_p_equals_np

end CurrentAdditive.V39PermittedOriginalDetYao
