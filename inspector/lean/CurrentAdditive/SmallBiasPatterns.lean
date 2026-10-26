import Paper2.FiniteSampling

/-!
# V27 small-bias pattern events (private candidate)

Source: `papers/randomized-additive-hardness/versions/2026-10-12-proof-exposition-v27/
source/sections/07a-small-bias.tex`, `yao:small-bias-patterns`.

The consumer is `yao:small-bias-escape`: the retained column set is measured
under the original labelled finite law, and each possible suffix output
pattern has small original-law mass. This module does not construct the
finite-field list or establish a communication lower bound.
-/

namespace CurrentAdditive.SmallBias

open scoped BigOperators

variable {Ω Λ : Type*} [Fintype Λ]

/-- The real sign of one Boolean bit: false has sign +1, true has sign -1. -/
def bitSign (b : Bool) : ℝ := if b then -1 else 1

/-- The parity character of a coordinate set, with the paper's sign convention. -/
def parityChar (S : Finset Ω) (w : Ω → Bool) : ℝ :=
  ∏ j ∈ S, bitSign (w j)

/-- The product convention is exactly the manuscript's
`(-1)^(sum of selected Boolean coordinates)`, with `true` interpreted as 1. -/
theorem parityChar_eq_pow (S : Finset Ω) (w : Ω → Bool) :
    parityChar S w =
      (-1 : ℝ) ^ (∑ j ∈ S, if w j then (1 : ℕ) else 0) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [parityChar]
  | @insert j S hj ih =>
      simp only [parityChar, Finset.prod_insert hj, Finset.sum_insert hj] at *
      rw [ih, pow_add]
      cases w j <;> simp [bitSign]

/-- The finite-law expectation of a parity character. Labelled duplicates
remain distinct elements of `Λ`. -/
def parityCorr (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool) (S : Finset Ω) : ℝ :=
  ∑ ℓ, μ.weight ℓ * parityChar S (word ℓ)

/-- Exact v27 small-bias premise: every nonempty parity is nearly balanced.
The empty character is deliberately excluded. -/
def IsSmallBiased (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool) (ε : ℝ) : Prop :=
  ∀ S : Finset Ω, S.Nonempty → |parityCorr μ word S| ≤ ε

/-- Sign of agreement with a prescribed bit. -/
def agreementSign (b z : Bool) : ℝ := if b = z then 1 else -1

def agreementChar (S : Finset Ω) (w z : Ω → Bool) : ℝ :=
  ∏ j ∈ S, agreementSign (w j) (z j)

private theorem agreementSign_eq (b z : Bool) :
    agreementSign b z = bitSign b * bitSign z := by
  cases b <;> cases z <;> norm_num [agreementSign, bitSign]

private theorem bitSign_abs (b : Bool) : |bitSign b| = 1 := by
  cases b <;> simp [bitSign]

private theorem agreementChar_eq (S : Finset Ω) (w z : Ω → Bool) :
    agreementChar S w z = parityChar S w * parityChar S z := by
  classical
  simp only [agreementChar, parityChar, agreementSign_eq, ← Finset.prod_mul_distrib]

private theorem parityChar_abs (S : Finset Ω) (w : Ω → Bool) :
    |parityChar S w| = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [parityChar]
  | @insert j S hj ih =>
      simp only [parityChar, Finset.prod_insert hj, abs_mul, bitSign_abs, one_mul] at *
      exact ih

private theorem agreement_expectation_eq
    (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool) (S : Finset Ω) (z : Ω → Bool) :
    (∑ ℓ, μ.weight ℓ * agreementChar S (word ℓ) z) =
      parityCorr μ word S * parityChar S z := by
  classical
  simp only [agreementChar_eq, parityCorr, Finset.sum_mul]
  congr 1
  funext ℓ
  ring

private theorem agreement_expectation_abs_le
    (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool) (ε : ℝ)
    (hμ : IsSmallBiased μ word ε) (S : Finset Ω) (hS : S.Nonempty)
    (z : Ω → Bool) :
    |∑ ℓ, μ.weight ℓ * agreementChar S (word ℓ) z| ≤ ε := by
  rw [agreement_expectation_eq, abs_mul, parityChar_abs, mul_one]
  exact hμ S hS

private theorem one_add_agreementSign (b z : Bool) :
    1 + agreementSign b z = if b = z then (2 : ℝ) else 0 := by
  cases b <;> cases z <;> norm_num [agreementSign]

private theorem pattern_product (I : Finset Ω) (w z : Ω → Bool) :
    (∏ j ∈ I, (1 + agreementSign (w j) (z j))) =
      if ∀ j ∈ I, w j = z j then (2 : ℝ) ^ I.card else 0 := by
  classical
  simp_rw [one_add_agreementSign]
  induction I using Finset.induction_on with
  | empty => simp
  | @insert j I hj ih =>
      simp only [Finset.prod_insert hj, Finset.card_insert_of_notMem hj,
        Finset.forall_mem_insert, ih]
      by_cases h : w j = z j <;> simp [h, pow_succ, mul_comm]

private theorem pattern_fourier (I : Finset Ω) (w z : Ω → Bool) :
    (∑ S ∈ I.powerset, agreementChar S w z) =
      if ∀ j ∈ I, w j = z j then (2 : ℝ) ^ I.card else 0 := by
  classical
  calc
    _ = ∑ S ∈ I.powerset, ∏ j ∈ S, agreementSign (w j) (z j) := rfl
    _ = ∏ j ∈ I, (1 + agreementSign (w j) (z j)) :=
      (Finset.prod_one_add I).symm
    _ = _ := pattern_product I w z

/-- V27 `yao:small-bias-patterns`, for a labelled finite law. The event is
evaluated under `μ` itself, including when the coordinate set and pattern
were selected after inspecting a proposed protocol. -/
theorem pattern_prob_le (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool)
    (ε : ℝ) (hε : 0 ≤ ε) (hμ : IsSmallBiased μ word ε)
    (I : Finset Ω) (z : Ω → Bool) :
    μ.prob (fun ℓ => ∀ j ∈ I, word ℓ j = z j) ≤
      (1 / 2 : ℝ) ^ I.card + ε := by
  classical
  let P := I.powerset
  let A : Finset Ω → ℝ := fun S =>
    ∑ ℓ, μ.weight ℓ * agreementChar S (word ℓ) z
  let q : ℝ := (2 : ℝ) ^ I.card
  have hq : 0 < q := by dsimp [q]; positivity
  have hzero : A ∅ = 1 := by
    simp [A, agreementChar, μ.total]
  have hsum : (∑ S ∈ P, A S) = q * μ.prob (fun ℓ => ∀ j ∈ I, word ℓ j = z j) := by
    dsimp [A, P, q]
    rw [Finset.sum_comm]
    calc
      (∑ ℓ, ∑ S ∈ I.powerset, μ.weight ℓ * agreementChar S (word ℓ) z) =
          ∑ ℓ, μ.weight ℓ *
            (∑ S ∈ I.powerset, agreementChar S (word ℓ) z) := by
              apply Finset.sum_congr rfl
              intro ℓ _
              exact (Finset.mul_sum _ _ _).symm
      _ = ∑ ℓ, μ.weight ℓ *
            (if ∀ j ∈ I, word ℓ j = z j then (2 : ℝ) ^ I.card else 0) := by
              apply Finset.sum_congr rfl
              intro ℓ _
              rw [pattern_fourier]
      _ = (2 : ℝ) ^ I.card * μ.prob
            (fun ℓ => ∀ j ∈ I, word ℓ j = z j) := by
              simp only [Paper2.FiniteLaw.prob, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro ℓ _
              split_ifs <;> ring
  have hmem : ∅ ∈ P := by simp [P]
  have hrest : ∑ S ∈ P.erase ∅, A S ≤ ((P.erase ∅).card : ℝ) * ε := by
    calc
      _ ≤ ∑ _S ∈ P.erase ∅, ε := by
        apply Finset.sum_le_sum
        intro S hS
        have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr
          (Finset.ne_of_mem_erase hS)
        exact (le_abs_self (A S)).trans
          (agreement_expectation_abs_le μ word ε hμ S hne z)
      _ = ((P.erase ∅).card : ℝ) * ε := by simp
  have hcard : ((P.erase ∅).card : ℝ) ≤ q := by
    have hnat : (P.erase ∅).card ≤ P.card :=
      Finset.card_le_card (Finset.erase_subset _ _)
    have hnat' : (P.erase ∅).card ≤ 2 ^ I.card := by
      simpa only [P, Finset.card_powerset] using hnat
    dsimp only [q]
    exact_mod_cast hnat'
  have hcover : q * μ.prob (fun ℓ => ∀ j ∈ I, word ℓ j = z j) ≤ 1 + q * ε := by
    rw [← hsum, ← Finset.sum_erase_add P A hmem, hzero]
    nlinarith [hrest, mul_le_mul_of_nonneg_right hcard hε]
  have hdiv : μ.prob (fun ℓ => ∀ j ∈ I, word ℓ j = z j) ≤ 1 / q + ε := by
    calc
      _ ≤ (1 + q * ε) / q := (le_div_iff₀ hq).2 (by nlinarith [hcover])
      _ = 1 / q + ε := by
        have hqn : q ≠ 0 := ne_of_gt hq
        field_simp
  simpa [q, one_div_pow] using hdiv

/-- The finite union form of `yao:small-bias-patterns`. This is the exact
mass-covering interface needed after the protocol cut chooses coordinates. -/
theorem patterns_prob_le (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool)
    (ε : ℝ) (hε : 0 ≤ ε) (hμ : IsSmallBiased μ word ε)
    (I : Finset Ω) (F : Finset (Ω → Bool)) :
    μ.prob (fun ℓ => ∃ z ∈ F, ∀ j ∈ I, word ℓ j = z j) ≤
      (F.card : ℝ) * ((1 / 2 : ℝ) ^ I.card + ε) := by
  calc
    _ ≤ ∑ z ∈ F, μ.prob (fun ℓ => ∀ j ∈ I, word ℓ j = z j) :=
      μ.prob_exists_le_sum F _
    _ ≤ ∑ _z ∈ F, ((1 / 2 : ℝ) ^ I.card + ε) := by
      apply Finset.sum_le_sum
      intro z _
      exact pattern_prob_le μ word ε hε hμ I z
    _ = (F.card : ℝ) * ((1 / 2 : ℝ) ^ I.card + ε) := by simp [mul_add]

/-- Abstract final contradiction at the v27 cut. `Y` is a set of labelled
columns with original-law mass at least `p`; every retained column is covered
by one of the fixed suffix patterns on `I`. No conditional law appears. -/
theorem no_retained_cover (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool)
    (ε p : ℝ) (hε : 0 ≤ ε) (hμ : IsSmallBiased μ word ε)
    (I : Finset Ω) (F : Finset (Ω → Bool)) (Y : Λ → Prop)
    (hretained : p ≤ μ.prob Y)
    (hcovered : ∀ ℓ, Y ℓ → ∃ z ∈ F, ∀ j ∈ I, word ℓ j = z j)
    (hshort : (F.card : ℝ) * ((1 / 2 : ℝ) ^ I.card + ε) < p) : False := by
  have hsubset := μ.prob_mono hcovered
  have hbound := patterns_prob_le μ word ε hε hμ I F
  linarith

#print axioms CurrentAdditive.SmallBias.parityChar_eq_pow
#print axioms CurrentAdditive.SmallBias.pattern_prob_le
#print axioms CurrentAdditive.SmallBias.patterns_prob_le
#print axioms CurrentAdditive.SmallBias.no_retained_cover

end CurrentAdditive.SmallBias
