import Paper2.YaoLowerBoundTapeEncoding
import Paper2.YaoLowerBoundTapePositions

/-!
# The actual fair-bit Yao matrix generator

Frozen v12 Appendix B `yao:random-bits` and Section 7 `yao:lift`.
Each selector address is decoded from its own `b` fair bits, and payload
bits are read directly. These positions have a fixed public count; no tape
is rejected, extended, or tested for a source promise. The full tape law
pushes forward to the exact sample law already used in the finite gap proof.
The encoded-machine running time and external SAT source remain separate.
-/

namespace Paper2.YaoLowerBound

open Paper2.Yao Paper2.YaoLookup

/-- Actual binary decoding, keeping every payload bit unchanged. -/
def decodeTape (t b lambda : ℕ) (tape : RandomTape t b lambda) :
    SelectorSamples t b lambda × PayloadSamples t b lambda :=
  (decodeSelectorArray (selectorCount t b lambda) (2 ^ (t - 1)) b tape.1, tape.2)

def decodeTapeEquiv (t b lambda : ℕ) :
    RandomTape t b lambda ≃ (SelectorSamples t b lambda × PayloadSamples t b lambda) :=
  (selectorArrayEquiv (selectorCount t b lambda) (2 ^ (t - 1)) b).prodCongr (Equiv.refl _)

@[simp] theorem decodeTapeEquiv_apply (t b lambda : ℕ) (tape : RandomTape t b lambda) :
    decodeTapeEquiv t b lambda tape = decodeTape t b lambda tape := rfl

theorem decodeTape_weight (t b lambda : ℕ) (tape : RandomTape t b lambda) :
    (structuredTapeLaw t b lambda).weight tape =
      (sampleLaw t b lambda).weight (decodeTape t b lambda tape) := by
  change (selectorArrayBitsLaw (selectorCount t b lambda) (2 ^ (t - 1)) b).weight tape.1 *
      ((payloadLaw (Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1))).iid
        (payloadCount t b lambda)).weight tape.2 = _
  rw [selectorArrayBitsLaw_weight]
  rfl

/-- Exact joint-law equality, including events depending on the full pair
of samples. It is stronger than separate coordinate marginal equalities. -/
theorem structuredTapeLaw_sample_prob (t b lambda : ℕ)
    (E : (SelectorSamples t b lambda × PayloadSamples t b lambda) → Prop) :
    (structuredTapeLaw t b lambda).prob (fun tape => E (decodeTape t b lambda tape)) =
      (sampleLaw t b lambda).prob E := by
  classical
  unfold FiniteLaw.prob
  simp_rw [decodeTape_weight]
  exact (decodeTapeEquiv t b lambda).sum_comp
    (fun samples => if E samples then (sampleLaw t b lambda).weight samples else 0)

/-- Read the finite Boolean tape and decode its address blocks. -/
def decodeFlatTape (t b lambda : ℕ) (tape : TapePosition t b lambda → Bool) :
    SelectorSamples t b lambda × PayloadSamples t b lambda :=
  decodeTape t b lambda ((tapeEquiv t b lambda).symm tape)

/-- Independent uniform bits on the exact public position set implement
the law in the communication-gap proof, with no exceptional tapes. -/
theorem flatTapeLaw_sample_prob (t b lambda : ℕ)
    (E : (SelectorSamples t b lambda × PayloadSamples t b lambda) → Prop) :
    (flatTapeLaw t b lambda).prob (fun tape => E (decodeFlatTape t b lambda tape)) =
      (sampleLaw t b lambda).prob E := by
  exact (flatTapeLaw_structured_prob t b lambda
    (fun tape => E (decodeTape t b lambda tape))).trans
    (structuredTapeLaw_sample_prob t b lambda E)

/-- A total executable matrix-entry generator from source incidence and
one finite fair-bit tape. Its input does not contain a colouring, a promise
test, an optimal protocol, or a successful-sampling certificate. -/
def matrixFromTape {V : Type*} [DecidableEq V] {edgeCount : ℕ}
    (t lambda : ℕ) (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ V)
    (tape : TapePosition t (paddedEdgeBits edgeCount) lambda → Bool) :
    (V × Fin (selectorCount t (paddedEdgeBits edgeCount) lambda)) →
      (Fin (2 ^ (t - 1)) × Fin (paddedEdgeCount edgeCount) ×
        Fin (payloadCount t (paddedEdgeBits edgeCount) lambda)) → Bool :=
  let samples := decodeFlatTape t (paddedEdgeBits edgeCount) lambda tape
  matrixEval (paddedEdgesEval edges) samples.1 samples.2

/-- Every tape has the stated charged communication upper bound on a
balanced source. There is no high-probability exception on YES instances. -/
theorem every_tape_yes_bound {V : Type*} [Fintype V] [DecidableEq V] {edgeCount : ℕ}
    (t lambda : ℕ) (ht : 1 ≤ t)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ V)
    (colour : V → Fin (2 ^ t))
    (hbalanced : ∀ e c, 2 ^ t - 1 ≤ colourFiberCard (fun i => colour (edges e i)) c)
    (tape : TapePosition t (paddedEdgeBits edgeCount) lambda → Bool) :
    Dalt .alice (matrixFromTape t lambda edges tape) ≤
      2 * paddedEdgeBits edgeCount + 4 * t + 2 :=
  paddedMatrixEval_balanced_budget t ht edges colour hbalanced _ _

theorem every_tape_universal_bound {V : Type*} [Fintype V] [DecidableEq V] {edgeCount : ℕ}
    (t lambda : ℕ) (ht : 1 ≤ t)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ V)
    (tape : TapePosition t (paddedEdgeBits edgeCount) lambda → Bool) :
    Dalt .alice (matrixFromTape t lambda edges tape) ≤
      (2 * paddedEdgeBits edgeCount + 4 * t + 2) + 2 * t :=
  paddedMatrixEval_universal_budget t ht edges _ _

/-- The finite NO guarantee now concerns the very same executable matrix
generator on unbiased Boolean tapes, not an ideal sampler substituted later. -/
theorem fair_tape_no_success {V : Type*} [Fintype V] [DecidableEq V] {edgeCount : ℕ}
    (t lambda : ℕ) (ht : 4 ≤ t) (hlambda : 0 < lambda)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ V)
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    1 - 2 * (1 / 2 : ℝ) ^ lambda ≤
      (flatTapeLaw t (paddedEdgeBits edgeCount) lambda).prob (fun tape =>
        (2 * paddedEdgeBits edgeCount + 4 * t + 2) + 2 * t - 6 ≤
          Dalt .alice (matrixFromTape t lambda edges tape)) := by
  exact (padded_matrix_success_prob_ge t lambda ht hlambda edges hno).trans_eq
    (flatTapeLaw_sample_prob t (paddedEdgeBits edgeCount) lambda (fun samples =>
      (2 * paddedEdgeBits edgeCount + 4 * t + 2) + 2 * t - 6 ≤
        Dalt .alice (matrixEval (paddedEdgesEval edges) samples.1 samples.2))).symm

/-- Every fixed finite gap, with success `511/512`, implemented by the
explicit finite fair-bit generator. Runtime and source reduction are not
silently inferred from this statement. -/
theorem fair_tape_fixed_gap_success
    {V : Type*} [Fintype V] [DecidableEq V] {edgeCount : ℕ}
    (g : ℕ) (edges : Fin edgeCount → Fin (2 ^ gapParameter g * 2 ^ gapParameter g) ↪ V)
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ gapParameter g - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    (511 / 512 : ℝ) ≤
      (flatTapeLaw (gapParameter g) (paddedEdgeBits edgeCount) 10).prob (fun tape =>
        (2 * paddedEdgeBits edgeCount + 4 * gapParameter g + 2) + g ≤
          Dalt .alice (matrixFromTape (gapParameter g) 10 edges tape)) := by
  obtain ⟨ht, hgap⟩ := gapParameter_admissible g
  have h := fair_tape_no_success (gapParameter g) 10 ht (by decide) edges hno
  norm_num only [show (1 - 2 * (1 / 2 : ℝ) ^ 10) = 511 / 512 by norm_num] at h
  apply h.trans
  apply FiniteLaw.prob_mono
  intro tape htape
  omega

end Paper2.YaoLowerBound
