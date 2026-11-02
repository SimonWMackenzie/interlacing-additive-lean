import CurrentAdditive.TrialSearch

/-!
Bridge under development: exact bit polynomial representation and long
division semantics. This new file does not alter the frozen executable files.
-/

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open Polynomial

noncomputable def polynomial (bound code : ℕ) : Polynomial (ZMod 2) :=
  ∑ i ∈ Finset.range bound, C (if code.testBit i then 1 else 0) * X ^ i

theorem coeff_polynomial (bound code j : ℕ) :
    (polynomial bound code).coeff j =
      if j < bound then (if code.testBit j then 1 else 0) else 0 := by
  classical
  unfold polynomial
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  simp [Finset.sum_ite_eq]

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
