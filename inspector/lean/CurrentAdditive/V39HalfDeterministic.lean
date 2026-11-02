import CurrentAdditive.V39HalfMidpoint
import CurrentAdditive.SmallBiasDetTapeAdapter

/-! Deterministic specialization of the same physical comparison classifier.
No separate numerical decoder or output-to-output comparison is introduced. -/

noncomputable section
open Classical

namespace CurrentAdditive.V39HalfDeterministic

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity
open CurrentAdditive.ModelEndpointReview
open CurrentAdditive.SmallBias
open CurrentAdditive.V39HalfMidpoint
open Paper2 Paper2.YaoBppDraft

/-- Actual deterministic bit-machine estimators embed with no random tape.
The numerical representation is arbitrary; only the supplied rational
comparison machine is used. -/
def ofDeterministic (est : List Bool → List Bool) (hpoly : BitMachine.Polytime est)
    (value : List Bool → ℝ) (R : HalfComparator value) (μ : YaoMeasure) (u : ℝ)
    (hacc : ∀ w c, AModel.targetYao μ w = some c → |value (est w) - (c : ℝ)| ≤ u) :
    HalfEstimator μ u where
  estimator := selectedDetEstimator est hpoly
  value := value
  comparator := R
  accurate := by
    intro w c hc
    rw [selectedDetEstimator_prob]
    simp only [if_pos (hacc w c hc)]
    norm_num

theorem ofDeterministic_zero (est : List Bool → List Bool) (hpoly : BitMachine.Polytime est)
    (value : List Bool → ℝ) (R : HalfComparator value) (μ : YaoMeasure) (u : ℝ)
    (hacc : ∀ w c, AModel.targetYao μ w = some c → |value (est w) - (c : ℝ)| ≤ u) :
    (ofDeterministic est hpoly value R μ u hacc).estimator.cR = 0 := rfl

private theorem prefix_tape (A : AModel.PrefixAlgorithm) (hp : A.Polynomial)
    (hR : ∃ c d : ℕ, ∀ n, A.tapeLength n = c * (n + 1) ^ d) (x : List Bool) :
    (SelectedTape.Algorithm.ofPrefixMonomial A hp hR).tapeLength x =
      A.tapeLength x.length := by
  change Classical.choose hR * (x.length + 1) ^
    Classical.choose (Classical.choose_spec hR) = _
  exact (Classical.choose_spec (Classical.choose_spec hR) x.length).symm

theorem classifier_tape_zero {μ : YaoMeasure} {u : ℝ}
    (E : HalfEstimator μ u) (hz : E.estimator.cR = 0) (x : List Bool) :
    E.classifier.tapeLength x = 0 := by
  have hh : (HeaderStrip.selectedEstimator E.estimator).cR = 0 := by
    simp [HeaderStrip.selectedEstimator, SelectedTape.pullback, hz]
  have heq : E.classifier.tapeLength x = E.majority.tapeLength x.length := by
    unfold HalfEstimator.classifier
    exact prefix_tape _ _ _ x
  rw [heq, E.majority_tape, hh]
  simp

/-- Any pullback of this deterministic estimator remains a zero-tape
physical decision algorithm. The printer is charged by pullback itself. -/
theorem pullback_tape_zero {μ : YaoMeasure} {u : ℝ}
    (E : HalfEstimator μ u) (hz : E.estimator.cR = 0)
    (f : List Bool → List Bool) (hf : BitMachine.Polytime f) (x : List Bool) :
    (SelectedTape.pullback f hf E.classifier).tapeLength x = 0 := by
  have hc : E.classifier.cR = 0 := by
    simpa [SelectedTape.Algorithm.tapeLength] using classifier_tape_zero E hz []
  simp [SelectedTape.pullback, SelectedTape.Algorithm.tapeLength, hc]

theorem classifier_output_singleton {μ : YaoMeasure} {u : ℝ}
    (E : HalfEstimator μ u) (word tape : List Bool) :
    ∃ b, E.classifier.output word tape = [b] := by
  unfold HalfEstimator.classifier SelectedTape.Algorithm.ofPrefixMonomial
  unfold HalfEstimator.majority ModelEndpointReview.RationalEndpoint.medAlgJudge
    ModelEndpointReview.RationalEndpoint.medOutputJudge
  exact ⟨_, rfl⟩

/-- Deterministic membership from an actual physical zero-tape classifier.
The decision premise here is a consumer of a proved source gap, not a
replacement source-construction premise. -/
theorem inP_of_decides {μ : YaoMeasure} {u : ℝ}
    (E : HalfEstimator μ u) (hz : E.estimator.cR = 0)
    (f : List Bool → List Bool) (hf : BitMachine.Polytime f)
    (L : BinaryLanguage)
    (hdec : (SelectedTape.pullback f hf E.classifier).Decides L (1 / 3)) :
    ComplexityReductionClosure.InP L := by
  let A := SelectedTape.pullback f hf E.classifier
  let decision := fun x => decide (A.output x [] = [true])
  have hzero : ∀ x, A.tapeLength x = 0 := pullback_tape_zero E hz f hf
  have hout : ∀ x, A.output x [] = [decision x] := by
    intro x
    have hs : ∃ b, A.output x [] = [b] := by
      rw [SelectedTape.pullback_output]
      exact classifier_output_singleton E _ _
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
    have hyes := (hdec x).1 hx
    rw [hzprob] at hyes
    by_contra hn
    have hn' : A.output x [] ≠ [true] := by simpa [decision] using hn
    simp [hn'] at hyes
    norm_num at hyes
  · intro hx
    by_contra hn
    have hno := (hdec x).2 hn
    have ht : A.output x [] = [true] := by simpa [decision] using hx
    rw [hzprob, if_pos ht] at hno
    norm_num at hno

#print axioms classifier_tape_zero
#print axioms pullback_tape_zero
#print axioms classifier_output_singleton
#print axioms inP_of_decides

end CurrentAdditive.V39HalfDeterministic
