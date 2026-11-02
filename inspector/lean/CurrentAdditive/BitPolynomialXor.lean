import CurrentAdditive.BitPolynomialBridge

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

theorem bit_xor_add (a b : Bool) :
    (if a ^^ b then (1 : ZMod 2) else 0) =
      (if a then 1 else 0) + (if b then 1 else 0) := by
  cases a <;> cases b <;> decide

theorem polynomial_xor (bound a b : ℕ) :
    polynomial bound (Nat.xor a b) = polynomial bound a + polynomial bound b := by
  ext j
  rw [coeff_polynomial, Polynomial.coeff_add, coeff_polynomial, coeff_polynomial]
  by_cases hj : j < bound
  · simp only [hj, ↓reduceIte]
    change (if (a ^^^ b).testBit j then (1 : ZMod 2) else 0) =
      (if a.testBit j then 1 else 0) + (if b.testBit j then 1 else 0)
    rw [Nat.testBit_xor]
    exact bit_xor_add (a.testBit j) (b.testBit j)
  · simp [hj]

#print axioms bit_xor_add
#print axioms polynomial_xor

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
