import EthInapproximability.CurrentPaper.SmallBiasSampler
import EthInapproximability.CurrentPaper.ExactFiniteReduction

/-!
# The two actual finite-field lists in the exact reduction

Source: locked v8 `E-exact-details.tex`, `lem:exact-families`.
The literal trace samplers and their two call-site definitions are already
implemented in `SmallBiasSampler`. This module proves polynomial bounds
for those same list lengths and supplies their balanced families to the
finite reduction. Original seed labels are retained, including collisions.

These are finite constructions and cardinality bounds. Mathlib's abstract
binary fields and their cardinality equivalences are noncomputable here;
constructing polynomial presentations and proving bit running time remain
separate obligations.
-/

namespace EthInapproximability.CurrentPaper.ExactSamplerInstances

open NPCC Workspace.Types.CommComplexity
open ExactConstruction SmallBiasSampler ExactFiniteReduction

/-- A positive binary exponent gives the minimum coordinate width. -/
theorem two_le_width {r : ℕ} (hr : 1 ≤ r) : 2 ≤ 2 ^ r := by
  have hp := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hr
  simpa using hp

/-- A convenient natural cutoff for the first sampler's bit length. -/
theorem firstWidth_le {a r : ℕ} (ha : 2 ≤ a) (har : a + 1 ≤ r) :
    prefixLength a + 3 ≤ 2 ^ r := by
  rw [exactFirst_width ha]
  have hpow : 1 ≤ (2 : ℕ) ^ a := Nat.one_le_pow _ _ (by omega)
  calc
    2 ^ a + 1 ≤ 2 ^ (a + 1) := by rw [pow_succ]; omega
    _ ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) har

/-- Polynomial upper bound for the actual first sampler. The scalar inputs
are satisfied by the manuscript's rounded widths beyond its fixed cutoff. -/
theorem firstSize_polynomial {a t d : ℕ} (hd : 2 ≤ d)
    (hq : prefixLength a + 3 ≤ d) (ht : 2 ^ t ≤ d ^ 128) :
    exactFirstSize a t d ≤ d ^ 300 := by
  have hraw := exactFirstSize_lt a t d hd
  have hpower : 2 ^ (2 * t) = (2 ^ t) ^ 2 := by rw [← pow_mul]; congr 1; omega
  rw [hpower] at hraw
  have hbound : 4 * (prefixLength a + 3) ^ 2 * d ^ 16 * (2 ^ t) ^ 2 ≤
      4 * d ^ 274 := by
    calc
      _ ≤ 4 * d ^ 2 * d ^ 16 * (d ^ 128) ^ 2 := by gcongr
      _ = _ := by ring
  have hfour : 4 ≤ d ^ 2 := by nlinarith
  have hfinal : 4 * d ^ 274 ≤ d ^ 300 := by
    calc
      _ ≤ d ^ 2 * d ^ 274 := Nat.mul_le_mul_right _ hfour
      _ = d ^ 276 := by rw [← pow_add]
      _ ≤ d ^ 300 := Nat.pow_le_pow_right (by omega) (by omega)
  exact hraw.le.trans (hbound.trans hfinal)

/-- Polynomial upper bound for the actual second sampler, on all `2^a`
alphabet labels before the duplicate-row map. -/
theorem secondSize_polynomial {a t d : ℕ} (ha : 0 < a) (hd : 2 ≤ d)
    (haSmall : a ≤ d) (ht : (2 ^ a) ^ t ≤ d ^ 18) :
    exactSecondSize a t d ≤ d ^ 100 := by
  have hraw := exactSecondSize_lt a t d ha hd
  have hpower : (2 ^ a) ^ (2 * t) = ((2 ^ a) ^ t) ^ 2 := by
    calc
      (2 ^ a) ^ (2 * t) = (2 ^ a) ^ (t * 2) := by rw [Nat.mul_comm 2 t]
      _ = ((2 ^ a) ^ t) ^ 2 := pow_mul _ _ _
  rw [hpower] at hraw
  have hbound : 4 * (d * a) ^ 2 * d ^ 16 * ((2 ^ a) ^ t) ^ 2 ≤
      4 * d ^ 56 := by
    calc
      _ ≤ 4 * (d * d) ^ 2 * d ^ 16 * (d ^ 18) ^ 2 := by gcongr
      _ = _ := by ring
  have hfour : 4 ≤ d ^ 2 := by nlinarith
  have hfinal : 4 * d ^ 56 ≤ d ^ 100 := by
    calc
      _ ≤ d ^ 2 * d ^ 56 := Nat.mul_le_mul_right _ hfour
      _ = d ^ 58 := by rw [← pow_add]
      _ ≤ d ^ 100 := Nat.pow_le_pow_right (by omega) (by omega)
  exact hraw.le.trans (hbound.trans hfinal)

/-- Exact first-list bounds when the coordinate width is `d=2^r`.
The lower bound is stronger than the paper's stated `d^64/2`. -/
theorem firstSize_bounds {a r t : ℕ} (hr : 1 ≤ r)
    (hq : prefixLength a + 3 ≤ 2 ^ r)
    (htq : t ≤ prefixLength a + 3)
    (htLow : 64 * r ≤ t) (htHigh : t ≤ 128 * r) :
    (2 ^ r) ^ 64 ≤ exactFirstSize a t (2 ^ r) ∧
      exactFirstSize a t (2 ^ r) ≤ (2 ^ r) ^ 300 := by
  constructor
  · apply le_trans ?_ (exactFirstSize_ge a t (2 ^ r) (two_le_width hr) htq)
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  · apply firstSize_polynomial (two_le_width hr) hq
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by omega)

/-- Exact second-list bounds. Both exponential comparisons reduce to the
displayed natural inequalities on `a*t`, with no real logarithm rounding. -/
theorem secondSize_bounds {a r t : ℕ} (ha : 0 < a) (hr : 1 ≤ r)
    (haSmall : a ≤ 2 ^ r) (htq : t ≤ 2 ^ r)
    (htLow : 6 * r ≤ a * t) (htHigh : a * t ≤ 18 * r) :
    (2 ^ r) ^ 6 ≤ exactSecondSize a t (2 ^ r) ∧
      exactSecondSize a t (2 ^ r) ≤ (2 ^ r) ^ 100 := by
  constructor
  · apply le_trans ?_ (exactSecondSize_ge a t (2 ^ r) ha (two_le_width hr) htq)
    simp only [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  · apply secondSize_polynomial ha (two_le_width hr) haSmall
    simp only [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by omega)

/-- Polynomial size of the actual matrix using the two trace samplers.
The row count includes every vector row, and the column count includes
the three auxiliary bits and all four independent selectors. -/
theorem matrix_size_polynomial {a r t₁ t₂ n : ℕ} (ha : 0 < a) (hr : 1 ≤ r)
    (hq : prefixLength a + 3 ≤ 2 ^ r) (haSmall : a ≤ 2 ^ r)
    (ht₁ : t₁ ≤ 128 * r) (ht₂ : a * t₂ ≤ 18 * r) :
    Fintype.card (Rows (exactSecondSize a t₂ (2 ^ r)) n) *
      Fintype.card (Columns (2 ^ r) (exactFirstSize a t₁ (2 ^ r))) ≤
      8 * (4 * (2 ^ r) ^ 100 + n) * (2 ^ r) ^ 1204 := by
  apply table_size_polynomial
  · apply firstSize_polynomial (two_le_width hr) hq
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  · apply secondSize_polynomial ha (two_le_width hr) haSmall
    simp only [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by omega)

/-- A change in the written list length is only an equality cast of seed
labels. It leaves every balancedness pattern count unchanged. -/
theorem balanced_cast_labels {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q N M t : ℕ} {ε : ℝ} (hNM : N = M) (C : Fin M → Fin q → Y)
    (hC : IsBalancedFamily t C ε) :
    IsBalancedFamily t (fun j i => C (Fin.cast hNM j) i) ε := by
  subst N
  simpa using hC

/-- Actual first-family instance in the finite theorem's dependent type. -/
noncomputable def firstFamilyFor (p : NumericParameters) (hr : 1 ≤ p.r)
    (hN₁ : p.N₁ = exactFirstSize p.a p.t₁ (2 ^ p.r)) : FirstFamily p.a p.N₁ :=
  fun j i => exactFirstFamily p.a p.t₁ (2 ^ p.r) (two_le_width hr) (Fin.cast hN₁ j) i

/-- Actual second-family instance on the full `2^a` alphabet. -/
noncomputable def secondFamilyFor (p : NumericParameters) (hr : 1 ≤ p.r)
    (hN₂ : p.N₂ = exactSecondSize p.a (2 ^ p.m₂) (2 ^ p.r)) :
    SecondFamily p.a (2 ^ p.r) p.N₂ :=
  fun j i => exactSecondFamily p.a (2 ^ p.m₂) (2 ^ p.r)
    (by have := p.ha; omega) (two_le_width hr) (Fin.cast hN₂ j) i

theorem firstFamilyFor_balanced (p : NumericParameters) (hr : 1 ≤ p.r)
    (hN₁ : p.N₁ = exactFirstSize p.a p.t₁ (2 ^ p.r))
    (hε : p.ε = 1 / ((2 ^ p.r : ℕ) : ℝ) ^ 8) :
    IsBalancedFamily p.t₁ (firstFamilyFor p hr hN₁) p.ε := by
  rw [hε]
  exact balanced_cast_labels hN₁ _ (exactFirstFamily_balanced p.a p.t₁ (2 ^ p.r)
    (two_le_width hr))

theorem secondFamilyFor_balanced (p : NumericParameters) (hr : 1 ≤ p.r)
    (hN₂ : p.N₂ = exactSecondSize p.a (2 ^ p.m₂) (2 ^ p.r))
    (hε : p.ε = 1 / ((2 ^ p.r : ℕ) : ℝ) ^ 8) :
    IsBalancedFamily (2 ^ p.m₂) (secondFamilyFor p hr hN₂) p.ε := by
  rw [hε]
  exact balanced_cast_labels hN₂ _ (exactSecondFamily_balanced p.a (2 ^ p.m₂)
    (2 ^ p.r) (by have := p.ha; omega) (two_le_width hr))

/-- The finite exact reduction instantiated with the actual field-pair
lists. Balancedness is proved here, not supplied by a sampler oracle.
Parameter production and bit-runtime remain separate obligations. -/
theorem decision_equivalence (p : NumericParameters) (hr : 1 ≤ p.r)
    (hN₁ : p.N₁ = exactFirstSize p.a p.t₁ (2 ^ p.r))
    (hN₂ : p.N₂ = exactSecondSize p.a (2 ^ p.m₂) (2 ^ p.r))
    (hε : p.ε = 1 / ((2 ^ p.r : ℕ) : ℝ) ^ 8)
    {n d : ℕ} (e : Fin d → Fin 2 → Fin n)
    (hD : 5 * d ≤ 2 ^ p.r) (hinj : ∀ α, Function.Injective (e α)) :
    D (matrix p.ha (firstFamilyFor p hr hN₁) (secondFamilyFor p hr hN₂)
      (sourceVectors (2 ^ p.r) e) (sourceVectors_cap (2 ^ p.r) e)) ≤
      p.a + 1 + p.r + 2 ↔
    ∃ colour : Fin n → Fin 4, ∀ α : Fin d, colour (e α 0) ≠ colour (e α 1) :=
  ExactFiniteReduction.decision_equivalence p _ _
    (firstFamilyFor_balanced p hr hN₁ hε) (secondFamilyFor_balanced p hr hN₂ hε)
    e hD hinj

end EthInapproximability.CurrentPaper.ExactSamplerInstances
