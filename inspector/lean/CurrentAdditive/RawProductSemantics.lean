import CurrentAdditive.PrinterResidueBound

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open Polynomial CurrentAdditive.FiniteFieldConstructor.BitPrinter

private theorem shifted_factor_polynomial (d b i : ℕ)
    (hb : b < 2 ^ d) (hi : i < d) :
    polynomial (2 * d) (b <<< i) = X ^ i * polynomial d b := by
  rw [polynomial_shift (2 * d) b i (by omega)]
  rw [polynomial_extend d (2 * d - i) b hb (by omega)]

private theorem fold_raw_polynomial (d a b : ℕ) (hb : b < 2 ^ d)
    (xs : List ℕ) (hxs : ∀ i ∈ xs, i < d) (acc : ℕ) :
    polynomial (2 * d)
        (xs.foldl (fun z i => if a.testBit i then Nat.xor z (b <<< i) else z) acc) =
      polynomial (2 * d) acc +
        (xs.map fun i =>
          if a.testBit i then X ^ i * polynomial d b else 0).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons i xs ih =>
      have hi : i < d := hxs i (by simp)
      have hxs' : ∀ j ∈ xs, j < d := by
        intro j hj
        exact hxs j (by simp [hj])
      rw [List.foldl_cons, ih hxs' _]
      simp only [List.map_cons, List.sum_cons]
      by_cases hbit : a.testBit i = true
      · simp only [hbit, ↓reduceIte]
        rw [polynomial_xor, shifted_factor_polynomial d b i hb hi]
        ring
      · have hfalse : a.testBit i = false := Bool.eq_false_iff.mpr hbit
        simp [hfalse]

theorem rawProduct_polynomial (d a b : ℕ) (hb : b < 2 ^ d) :
    polynomial (2 * d) (rawProduct d a b) =
      polynomial d a * polynomial d b := by
  unfold rawProduct
  have hfold := fold_raw_polynomial d a b hb (List.range d)
    (by intro i hi; simpa using hi) 0
  have hsum :
      ((List.range d).map fun i =>
          if a.testBit i then X ^ i * polynomial d b else 0).sum =
        ∑ i ∈ Finset.range d,
          if a.testBit i then X ^ i * polynomial d b else 0 := by
    rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  have hzero : polynomial (2 * d) 0 = 0 := by simp [polynomial]
  rw [hzero, zero_add, hsum] at hfold
  rw [hfold]
  simp only [polynomial, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  cases hbit : a.testBit i <;> simp [hbit]

#print axioms rawProduct_polynomial

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
