import CurrentAdditive.BitPolynomialXor

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open Polynomial

theorem polynomial_shift (bound a s : ℕ) (hs : s ≤ bound) :
    polynomial bound (a <<< s) = X ^ s * polynomial (bound - s) a := by
  ext j
  rw [coeff_polynomial, Polynomial.coeff_X_pow_mul', coeff_polynomial]
  change (if j < bound then
    (if (a <<< s).testBit j then (1 : ZMod 2) else 0) else 0) =
    if s ≤ j then
      (if j - s < bound - s then
        (if a.testBit (j - s) then 1 else 0) else 0) else 0
  rw [Nat.testBit_shiftLeft]
  by_cases hsj : s ≤ j
  · have hdec : decide (j ≥ s) = true := by simp [hsj]
    rw [hdec]
    simp only [Bool.true_and]
    by_cases hjb : j < bound
    · have hsmall : j - s < bound - s := by omega
      simp [hsj, hjb, hsmall]
    · have hlarge : ¬ j - s < bound - s := by omega
      simp [hsj, hjb, hlarge]
  · have hdec : decide (j ≥ s) = false := by simp [hsj]
    rw [hdec]
    simp [hsj]

#print axioms polynomial_shift

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
