import Paper2.YaoLowerBoundProbability
import Paper2.CappedSamplerBits

/-!
# Exact fair-bit positions for the Yao construction

Frozen v12 Appendix B, `yao:materialization` and `yao:random-bits`.
The structured selector-bit and payload arrays are explicitly equivalent
to one Boolean bit for each position in their disjoint union. Their laws
are equal under this equivalence for arbitrary events. No rejection or
promise-dependent tape length is involved, including when `b=0`.
-/

namespace Paper2.YaoLowerBound

open Paper2.Yao
open scoped BigOperators

/-- Exactly `b` bits for each labelled selector address. -/
abbrev SelectorBitSamples (t b lambda : ℕ) :=
  Fin (selectorCount t b lambda) → Fin (2 ^ (t - 1)) → Fin b → Bool

/-- All random data before selector addresses are decoded. -/
abbrev RandomTape (t b lambda : ℕ) :=
  SelectorBitSamples t b lambda × PayloadSamples t b lambda

/-- A tagged selector-bit or payload-bit position. The tags keep all
labelled draws distinct even when their sampled values coincide. -/
abbrev TapePosition (t b lambda : ℕ) :=
  (Fin (selectorCount t b lambda) × Fin (2 ^ (t - 1)) × Fin b) ⊕
    (Fin (payloadCount t b lambda) × (Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1)))

/-- The exact number of unbiased bits in the manuscript. -/
def tapeBitCount (t b lambda : ℕ) : ℕ :=
  selectorCount t b lambda * 2 ^ (t - 1) * b +
    payloadCount t b lambda * 2 ^ b * (2 ^ t * 2 ^ t + 1)

theorem card_tapePosition (t b lambda : ℕ) :
    Fintype.card (TapePosition t b lambda) = tapeBitCount t b lambda := by
  simp [TapePosition, tapeBitCount, Nat.mul_assoc]

/-- Read a flat bit position from the structured arrays. -/
def tapeEquiv (t b lambda : ℕ) :
    RandomTape t b lambda ≃ (TapePosition t b lambda → Bool) where
  toFun tape
    | .inl (z, g, j) => tape.1 z g j
    | .inr (l, p) => tape.2 l p
  invFun tape := (fun z g j => tape (.inl (z, g, j)),
    fun l p => tape (.inr (l, p)))
  left_inv tape := rfl
  right_inv tape := by
    funext p
    cases p with
    | inl p => rfl
    | inr p => rfl

@[simp] theorem tapeEquiv_selector (t b lambda : ℕ) (tape : RandomTape t b lambda)
    (z : Fin (selectorCount t b lambda)) (g : Fin (2 ^ (t - 1))) (j : Fin b) :
    tapeEquiv t b lambda tape (.inl (z, g, j)) = tape.1 z g j := rfl

@[simp] theorem tapeEquiv_payload (t b lambda : ℕ) (tape : RandomTape t b lambda)
    (l : Fin (payloadCount t b lambda)) (p : Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1)) :
    tapeEquiv t b lambda tape (.inr (l, p)) = tape.2 l p := rfl

/-- Independent fair bits grouped by selector label, address coordinate,
and bit coordinate, independently of all labelled payload words. -/
noncomputable def structuredTapeLaw (t b lambda : ℕ) :
    FiniteLaw (RandomTape t b lambda) :=
  ((FiniteLaw.pi (fun _ : Fin (2 ^ (t - 1)) => CappedSampler.fairBits b)).iid
      (selectorCount t b lambda)).prod
    ((payloadLaw (Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1))).iid
      (payloadCount t b lambda))

/-- One independent uniform Boolean bit per public tape position. -/
noncomputable def flatTapeLaw (t b lambda : ℕ) :
    FiniteLaw (TapePosition t b lambda → Bool) :=
  FiniteLaw.pi (fun _ : TapePosition t b lambda => FiniteLaw.uniform Bool)

theorem structuredTapeLaw_weight (t b lambda : ℕ) (tape : RandomTape t b lambda) :
    (structuredTapeLaw t b lambda).weight tape =
      (1 / 2 : ℝ) ^ tapeBitCount t b lambda := by
  simp only [structuredTapeLaw, FiniteLaw.prod, FiniteLaw.iid, FiniteLaw.pi,
    CappedSampler.fairBits_weight, payloadLaw, FiniteLaw.uniform,
    Fintype.card_bool, Nat.cast_ofNat, ← inv_pow, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Fintype.card_prod]
  simp only [tapeBitCount, one_div, ← pow_mul, ← pow_add]
  congr 1
  ring

theorem flatTapeLaw_weight (t b lambda : ℕ)
    (tape : TapePosition t b lambda → Bool) :
    (flatTapeLaw t b lambda).weight tape =
      (1 / 2 : ℝ) ^ tapeBitCount t b lambda := by
  simp [flatTapeLaw, FiniteLaw.pi, FiniteLaw.uniform, tapeBitCount, Nat.mul_assoc]

/-- Reshaping the fair tape into its structured arrays preserves every
event, not just marginal events of individual selector or payload bits. -/
theorem flatTapeLaw_structured_prob (t b lambda : ℕ)
    (E : RandomTape t b lambda → Prop) :
    (flatTapeLaw t b lambda).prob (fun tape => E ((tapeEquiv t b lambda).symm tape)) =
      (structuredTapeLaw t b lambda).prob E := by
  classical
  unfold FiniteLaw.prob
  simp_rw [structuredTapeLaw_weight, flatTapeLaw_weight]
  exact (tapeEquiv t b lambda).symm.sum_comp
    (fun tape => if E tape then (1 / 2 : ℝ) ^ tapeBitCount t b lambda else 0)

/-- The same event identity in the direction of flattening the arrays. -/
theorem structuredTapeLaw_flat_prob (t b lambda : ℕ)
    (E : (TapePosition t b lambda → Bool) → Prop) :
    (structuredTapeLaw t b lambda).prob (fun tape => E (tapeEquiv t b lambda tape)) =
      (flatTapeLaw t b lambda).prob E := by
  classical
  unfold FiniteLaw.prob
  simp_rw [structuredTapeLaw_weight, flatTapeLaw_weight]
  exact (tapeEquiv t b lambda).sum_comp
    (fun tape => if E tape then (1 / 2 : ℝ) ^ tapeBitCount t b lambda else 0)

end Paper2.YaoLowerBound
