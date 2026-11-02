import CurrentAdditive.V39ActualOutputMajority
import CurrentAdditive.V39YaoEndpointJoin

/-!
Corrected valid-input numerical-output boundary. Comparison semantics are
required only on actual estimator outputs at valid encoded matrices. The
source table, its cost gap, physical header adapter and source compiler are
the already checked same objects. The whole encoded table printer remains
an explicit unresolved construction premise.
-/

noncomputable section
open Classical

namespace CurrentAdditive.V39ActualYaoEndpoint

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity
open CurrentAdditive.V39ActualOutputMajority
open CurrentAdditive.V39FramedComparator
open CurrentAdditive.V39YaoEndpointJoin
open CurrentAdditive.V38Source
open CurrentAdditive.SmallBias
open Paper2 Paper2.Yao Paper2.YaoBppDraft

/-- Numerical accuracy is guarded by the valid-matrix target. Comparison
correctness is supplied locally below, at the one selected word/midpoint,
so no arbitrarily long rational requests or malformed input are included. -/
structure ValidYaoEstimator (μ : YaoMeasure) (u : ℝ) where
  algorithm : ActualEstimator
  accurate : ∀ word c, AModel.targetYao μ word = some c →
    2 / 3 ≤ algorithm.estimator.prob word
      (fun out => |algorithm.value out - (c : ℝ)| ≤ u)

theorem ValidYaoEstimator.matrix_law {μ : YaoMeasure} {u : ℝ}
    (E : ValidYaoEstimator μ u) (hu : 0 ≤ u) (i : Instance) (hi : i.Valid) (B k : ℕ)
    (hgap : 2 * (u + 2) < (k : ℝ))
    (hcompare : E.algorithm.actualComparison
      (AModel.matrixWord i.rows i.cols i.table) (2 * B + k)) :
    (Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table) ≤ B →
      99 / 100 < E.algorithm.classifier.prob
        (natField (2 * B + k) ++ AModel.matrixWord i.rows i.cols i.table) (· = [true])) ∧
    (B + k ≤ Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table) →
      E.algorithm.classifier.prob
        (natField (2 * B + k) ++ AModel.matrixWord i.rows i.cols i.table) (· = [true]) < 1 / 100) := by
  let D := Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table)
  let word := AModel.matrixWord i.rows i.cols i.table
  have ht := YaoSelected.target_matrix μ i hi
  have hmodel := V39RationalMidpoint.four_model_comparison μ i hi
  have hacc := E.accurate word (μ.eval i) ht
  have hevent : ∀ out, |E.algorithm.value out - (μ.eval i : ℝ)| ≤ u →
      |E.algorithm.value out - (D : ℝ)| ≤ u + 2 := by
    intro out hout
    have h := abs_sub_le (E.algorithm.value out) (μ.eval i : ℝ) (D : ℝ)
    change |(μ.eval i : ℝ) - (D : ℝ)| ≤ 2 at hmodel
    linarith
  have hacc' : 2 / 3 ≤ E.algorithm.estimator.prob word
      (fun out => |E.algorithm.value out - (D : ℝ)| ≤ u + 2) := by
    refine hacc.trans ?_
    apply FiniteLaw.prob_mono
    intro tape hgood
    exact hevent _ hgood
  exact E.algorithm.fixed_midpoint_strict_law word D B k (u + 2)
    (by linarith) hgap hcompare hacc'

def ValidYaoEstimator.sourceDecider {μ : YaoMeasure} {u : ℝ}
    (E : ValidYaoEstimator μ u) {t : ℕ} (G : GLSourceInput t)
    (hp : BitMachine.Polytime (sourceWord G)) : SelectedTape.Algorithm :=
  SelectedTape.pullback (sourceWord G) hp E.algorithm.classifier

theorem ValidYaoEstimator.source_decides {μ : YaoMeasure} {u : ℝ}
    (E : ValidYaoEstimator μ u) (hu : 0 ≤ u) {t : ℕ} (G : GLSourceInput t)
    (ht : 4 ≤ t) (hgap : 2 * (u + 2) < ((2 * t - 8 : ℕ) : ℝ))
    (hp : BitMachine.Polytime (sourceWord G))
    (hcompare : ∀ input, E.algorithm.actualComparison
      (AModel.matrixWord (selectedInstance G input).rows (selectedInstance G input).cols
        (selectedInstance G input).table)
      (2 * (selectedInstance G input).threshold + (2 * t - 8))) :
    (E.sourceDecider G hp).Decides G.L (1 / 3) := by
  intro input
  have h := E.matrix_law hu (selectedInstance G input)
    (V39SourceRenderer.selectedInstance_valid G input)
    (selectedInstance G input).threshold (2 * t - 8) hgap (hcompare input)
  have hg := selectedInstance_gap G ht input
  constructor
  · intro hx
    have hh := h.1 (hg.1 hx)
    change 99 / 100 < E.algorithm.classifier.prob (sourceWord G input) (· = [true]) at hh
    rw [ValidYaoEstimator.sourceDecider, SelectedTape.pullback_prob]
    change 1 - (1 / 3 : ℝ) ≤ E.algorithm.classifier.prob (sourceWord G input) (· = [true])
    linarith
  · intro hx
    have hh := h.2 (hg.2 hx)
    change E.algorithm.classifier.prob (sourceWord G input) (· = [true]) < 1 / 100 at hh
    rw [ValidYaoEstimator.sourceDecider, SelectedTape.pullback_prob]
    change E.algorithm.classifier.prob (sourceWord G input) (· = [true]) ≤ (1 / 3 : ℝ)
    linarith

private theorem prefix_tape (A : AModel.PrefixAlgorithm) (hp : A.Polynomial)
    (hR : ∃ c d : ℕ, ∀ n, A.tapeLength n = c * (n + 1) ^ d) (x : List Bool) :
    (SelectedTape.Algorithm.ofPrefixMonomial A hp hR).tapeLength x = A.tapeLength x.length := by
  change Classical.choose hR * (x.length + 1) ^
    Classical.choose (Classical.choose_spec hR) = _
  exact (Classical.choose_spec (Classical.choose_spec hR) x.length).symm

theorem actual_classifier_zero (E : ActualEstimator) (hz : E.estimator.cR = 0)
    (word : List Bool) : E.classifier.tapeLength word = 0 := by
  have hh : (HeaderStrip.selectedEstimator E.estimator).cR = 0 := by
    simp [HeaderStrip.selectedEstimator, SelectedTape.pullback, hz]
  have heq : E.classifier.tapeLength word = E.majority.tapeLength word.length := by
    unfold ActualEstimator.classifier
    exact prefix_tape _ _ _ word
  rw [heq, E.majority_tape, hh]
  simp

theorem actual_classifier_singleton (E : ActualEstimator) (word tape : List Bool) :
    ∃ b, E.classifier.output word tape = [b] := by
  unfold ActualEstimator.classifier SelectedTape.Algorithm.ofPrefixMonomial
  unfold ActualEstimator.majority ModelEndpointReview.RationalEndpoint.medAlgJudge
    ModelEndpointReview.RationalEndpoint.medOutputJudge
  exact ⟨_, rfl⟩

/-- Deterministic extraction uses the same physical zero-tape classifier
and the existing checked zeroTapeOutputPolytime adapter. -/
theorem actual_inP_of_decides (E : ActualEstimator) (hz : E.estimator.cR = 0)
    (f : List Bool → List Bool) (hf : BitMachine.Polytime f) (L : BinaryLanguage)
    (hd : (SelectedTape.pullback f hf E.classifier).Decides L (1 / 3)) :
    ComplexityReductionClosure.InP L := by
  let A := SelectedTape.pullback f hf E.classifier
  let decision := fun x => decide (A.output x [] = [true])
  have hc : E.classifier.cR = 0 := by
    simpa [SelectedTape.Algorithm.tapeLength] using actual_classifier_zero E hz []
  have hzero : ∀ x, A.tapeLength x = 0 := by
    intro x
    simp [A, SelectedTape.pullback, SelectedTape.Algorithm.tapeLength, hc]
  have hout : ∀ x, A.output x [] = [decision x] := by
    intro x
    have hs : ∃ b, A.output x [] = [b] := by
      rw [SelectedTape.pullback_output]
      exact actual_classifier_singleton E _ _
    obtain ⟨b, hb⟩ := hs
    dsimp [decision]
    rw [hb]
    cases b <;> simp
  have hp : BitMachine.Polytime (fun x => [decision x]) := by
    have h := zeroTapeOutputPolytime A hzero
    have heq : (fun x => A.output x []) = (fun x => [decision x]) := by
      funext x
      exact hout x
    rwa [heq] at h
  refine ⟨decision, hp, ?_⟩
  intro x
  have hzprob := zeroTapeProb A hzero x (· = [true])
  constructor
  · intro hx
    have hyes := (hd x).1 hx
    rw [hzprob] at hyes
    by_contra hn
    have hn' : A.output x [] ≠ [true] := by simpa [decision] using hn
    simp [hn'] at hyes
    norm_num at hyes
  · intro hx
    by_contra hn
    have hno := (hd x).2 hn
    have ht : A.output x [] = [true] := by simpa [decision] using hx
    rw [hzprob, if_pos ht] at hno
    norm_num at hno

theorem actual_np_subset_bpp_fixed_error (u : ℝ) (hu : 0 ≤ u)
    (G : GLSourceInput (estimatorParameter u)) (hard : NPHard G.L)
    {μ : YaoMeasure} (E : ValidYaoEstimator μ u)
    (hencoded : BitMachine.Polytime (fun input => encodeInstance (selectedInstance G input)))
    (hcompare : ∀ input, E.algorithm.actualComparison
      (AModel.matrixWord (selectedInstance G input).rows (selectedInstance G input).cols
        (selectedInstance G input).table)
      (2 * (selectedInstance G input).threshold + (2 * estimatorParameter u - 8))) :
    ∀ L, InNP L → SelectedTape.InBPP L := by
  have hk : 0 < 2 * estimatorParameter u - 8 := by
    have h := estimatorParameter_gap u
    have hh : (0 : ℝ) < ((2 * estimatorParameter u - 8 : ℕ) : ℝ) := by linarith
    exact_mod_cast hh
  let hp := sourceWord_polytime_of_encoded G hk hencoded
  exact SelectedTape.np_subset_inBPP hard
    ⟨E.sourceDecider G hp,
      E.source_decides hu G (estimatorParameter_valid u) (estimatorParameter_gap u) hp hcompare⟩

theorem actual_p_equals_np_fixed_error (u : ℝ) (hu : 0 ≤ u)
    (G : GLSourceInput (estimatorParameter u)) (hard : NPHard G.L)
    {μ : YaoMeasure} (E : ValidYaoEstimator μ u) (hz : E.algorithm.estimator.cR = 0)
    (hencoded : BitMachine.Polytime (fun input => encodeInstance (selectedInstance G input)))
    (hcompare : ∀ input, E.algorithm.actualComparison
      (AModel.matrixWord (selectedInstance G input).rows (selectedInstance G input).cols
        (selectedInstance G input).table)
      (2 * (selectedInstance G input).threshold + (2 * estimatorParameter u - 8))) :
    PEqualsNP := by
  have hk : 0 < 2 * estimatorParameter u - 8 := by
    have h := estimatorParameter_gap u
    have hh : (0 : ℝ) < ((2 * estimatorParameter u - 8 : ℕ) : ℝ) := by linarith
    exact_mod_cast hh
  let hp := sourceWord_polytime_of_encoded G hk hencoded
  have hmem : ComplexityReductionClosure.InP G.L :=
    actual_inP_of_decides E.algorithm hz (sourceWord G) hp G.L
      (E.source_decides hu G (estimatorParameter_valid u) (estimatorParameter_gap u) hp hcompare)
  exact p_equals_np_of_np_subset_p
    (ComplexityReductionClosure.npHard_inP_implies_np_subset_p hard hmem)

#print axioms ValidYaoEstimator.matrix_law
#print axioms ValidYaoEstimator.source_decides
#print axioms actual_classifier_zero
#print axioms actual_inP_of_decides
#print axioms actual_np_subset_bpp_fixed_error
#print axioms actual_p_equals_np_fixed_error

end CurrentAdditive.V39ActualYaoEndpoint
