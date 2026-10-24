import CurrentAdditive.MonicBits

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

theorem polynomial_extend (small big code : ℕ)
    (hsize : code < 2 ^ small) (hbound : small ≤ big) :
    polynomial big code = polynomial small code := by
  ext j
  rw [coeff_polynomial, coeff_polynomial]
  by_cases hj : j < small
  · have hjbig : j < big := by omega
    simp [hj, hjbig]
  · have hpow : 2 ^ small ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    have hbit : code.testBit j = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hsize hpow)
    simp [hj, hbit]

#print axioms polynomial_extend

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
