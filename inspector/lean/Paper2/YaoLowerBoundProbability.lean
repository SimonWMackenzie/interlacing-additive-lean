import Paper2.YaoLowerBound
import Paper2.YaoSelectorEventsBound
import Paper2.YaoLookupEvaluation

/-!
# The finite randomized Yao communication gap

Frozen v12 Section 7 `yao:lift`, using Appendix B's explicit sample counts.
The law samples all selector tuples and all payload words independently.
The resulting entry function is the same matrix as in the upper-bound and
restriction proofs. This completes the finite probabilistic implication
from the explicit hypergraph promises, not the external source reduction or
the encoded-machine running-time/random-tape implementation.
-/

namespace Paper2.YaoLowerBound

open Paper2.Yao Paper2.YaoLookup

variable {V E : Type*} [Fintype V]

/-- The manuscript's fixed public number of selector labels. -/
def selectorCount (t b lambda : ℕ) : ℕ :=
  selectorSampleCount (2 ^ (t - 1)) (2 ^ b) (2 ^ (2 ^ t - 1)) lambda

/-- The manuscript's fixed public number of payload labels; the first
argument is the exact number `H*(K+1)` of payload positions. -/
def payloadCount (t b lambda : ℕ) : ℕ :=
  payloadSampleCount (2 ^ b * (2 ^ t * 2 ^ t + 1))
    (b + 3 * t - 3) (payloadDelta b t) lambda

abbrev SelectorSamples (t b lambda : ℕ) :=
  Fin (selectorCount t b lambda) → Fin (2 ^ (t - 1)) → Fin (2 ^ b)

abbrev PayloadSamples (t b lambda : ℕ) :=
  Fin (payloadCount t b lambda) → Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1) → Bool

/-- All sampled entries are independent, with indexed repetitions retained.
The law depends only on the public parameters, not on the source promise. -/
noncomputable def sampleLaw (t b lambda : ℕ) :
    FiniteLaw (SelectorSamples t b lambda × PayloadSamples t b lambda) :=
  ((selectorLaw (2 ^ (t - 1)) (2 ^ b)).iid (selectorCount t b lambda)).prod
    ((payloadLaw (Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1))).iid (payloadCount t b lambda))

theorem selectorCount_positive (t b lambda : ℕ) (hlambda : 0 < lambda) :
    0 < selectorCount t b lambda :=
  selectorSampleCount_positive _ _ _ _ (pow_pos (by decide) _) hlambda

/-- Exact two-event probability accounting for the actual sampled matrix.
The protocol and its retained rows may depend on both complete samples. -/
theorem communication_failure_prob_le (t b lambda : ℕ) (ht : 4 ≤ t)
    (hlambda : 0 < lambda)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V) (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    (sampleLaw t b lambda).prob (fun samples =>
      Dalt .alice (matrix (placeEdges edges index) samples.1 samples.2) <
        (2 * b + 4 * t + 2) + 2 * t - 6) ≤ 2 * (1 / 2 : ℝ) ^ lambda := by
  let μ := (selectorLaw (2 ^ (t - 1)) (2 ^ b)).iid (selectorCount t b lambda)
  let ν := (payloadLaw (Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1))).iid
    (payloadCount t b lambda)
  have hfirst : μ.prob (fun C => ¬ selectorGood (2 ^ (t - 1)) (2 ^ b)
      (2 ^ (2 ^ t - 1)) (selectorCount t b lambda) C) ≤ (1 / 2 : ℝ) ^ lambda :=
    selector_explicit_counts_failure_le _ _ _ _ (pow_pos (by decide) _) hlambda
  have hsecond : ν.prob (payloadShortProtocolFailure (b + 3 * t - 3) t
      (payloadMinimum b t) (payloadCount t b lambda)) ≤ (1 / 2 : ℝ) ^ lambda := by
    have hp := payload_explicit_counts_short_failure_le
      (X := Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1)) b t lambda ht
    dsimp only at hp
    have hcard : Fintype.card (Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1)) =
        2 ^ b * (2 ^ t * 2 ^ t + 1) := by simp
    rw [hcard] at hp
    exact hp
  have hbound := FiniteLaw.two_stage_failure_le μ ν
    (selectorGood (2 ^ (t - 1)) (2 ^ b) (2 ^ (2 ^ t - 1)) (selectorCount t b lambda))
    (fun C W => Dalt .alice (matrix (placeEdges edges index) C W) <
      (2 * b + 4 * t + 2) + 2 * t - 6)
    ((1 / 2 : ℝ) ^ lambda) ((1 / 2 : ℝ) ^ lambda) hfirst
    (fun C hC => (FiniteLaw.prob_mono ν (fun W hbad => by
      by_contra hW
      have hlow := lower_bound_of_good_events t b ht
        (selectorCount_positive t b lambda hlambda) edges index hno C hC W hW
      omega)).trans hsecond) (by positivity)
  simpa only [sampleLaw, μ, ν, two_mul] using hbound

private theorem prob_add_not {X : Type*} [Fintype X] (μ : FiniteLaw X) (A : X → Prop) :
    μ.prob A + μ.prob (fun x => ¬ A x) = 1 := by
  classical
  rw [FiniteLaw.prob, FiniteLaw.prob, ← Finset.sum_add_distrib]
  calc
    _ = ∑ x, μ.weight x := Finset.sum_congr rfl (fun x _ => by by_cases h : A x <;> simp [h])
    _ = 1 := μ.total

/-- Finite probability statement in the form used by `yao:lift`. At
`lambda=10`, the success probability is at least `511/512`. -/
theorem communication_success_prob_ge (t b lambda : ℕ) (ht : 4 ≤ t)
    (hlambda : 0 < lambda)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V) (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    1 - 2 * (1 / 2 : ℝ) ^ lambda ≤
      (sampleLaw t b lambda).prob (fun samples =>
        (2 * b + 4 * t + 2) + 2 * t - 6 ≤
          Dalt .alice (matrix (placeEdges edges index) samples.1 samples.2)) := by
  have hfail := communication_failure_prob_le t b lambda ht hlambda edges index hno
  have hsum := prob_add_not (sampleLaw t b lambda)
    (fun samples => Dalt .alice (matrix (placeEdges edges index) samples.1 samples.2) <
      (2 * b + 4 * t + 2) + 2 * t - 6)
  simp only [not_lt] at hsum
  linarith

theorem communication_success_prob_ten (t b : ℕ) (ht : 4 ≤ t)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V) (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    (511 / 512 : ℝ) ≤ (sampleLaw t b 10).prob (fun samples =>
      (2 * b + 4 * t + 2) + 2 * t - 6 ≤
        Dalt .alice (matrix (placeEdges edges index) samples.1 samples.2)) := by
  convert communication_success_prob_ge t b 10 ht (by decide) edges index hno using 1
  norm_num

/-- The same probability theorem for the executable entry evaluator and
the least-power-of-two edge-padding compiler. -/
theorem padded_matrix_success_prob_ge [DecidableEq V] {edgeCount : ℕ}
    (t lambda : ℕ) (ht : 4 ≤ t) (hlambda : 0 < lambda)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ V)
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    1 - 2 * (1 / 2 : ℝ) ^ lambda ≤
      (sampleLaw t (paddedEdgeBits edgeCount) lambda).prob (fun samples =>
        (2 * paddedEdgeBits edgeCount + 4 * t + 2) + 2 * t - 6 ≤
          Dalt .alice (matrixEval (paddedEdgesEval edges) samples.1 samples.2)) := by
  simpa only [matrixEval_eq, paddedEdgesEval_eq] using
    communication_success_prob_ge t (paddedEdgeBits edgeCount) lambda ht hlambda
      edges (Fin.castLEEmb (le_paddedEdgeCount edgeCount)) hno

/-- The fixed-gap choice in the proof of `yao:main`: the integer expression
is `max(4,ceil((g+6)/2))`, computed without inspecting the source promise. -/
def gapParameter (g : ℕ) : ℕ := max 4 ((g + 7) / 2)

theorem gapParameter_admissible (g : ℕ) : 4 ≤ gapParameter g ∧ g + 6 ≤ 2 * gapParameter g := by
  unfold gapParameter
  omega

/-- Every fixed gap at the finite sampled-matrix level, from the explicit
colouring promise. This is not yet a SAT-to-table runtime theorem. -/
theorem fixed_gap_success_prob (g b : ℕ)
    (edges : E → Fin (2 ^ gapParameter g * 2 ^ gapParameter g) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ gapParameter g - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    (511 / 512 : ℝ) ≤ (sampleLaw (gapParameter g) b 10).prob (fun samples =>
      (2 * b + 4 * gapParameter g + 2) + g ≤
        Dalt .alice (matrix (placeEdges edges index) samples.1 samples.2)) := by
  obtain ⟨ht, hgap⟩ := gapParameter_admissible g
  apply (communication_success_prob_ten (gapParameter g) b ht edges index hno).trans
  apply FiniteLaw.prob_mono
  intro samples hsamples
  omega

end Paper2.YaoLowerBound
