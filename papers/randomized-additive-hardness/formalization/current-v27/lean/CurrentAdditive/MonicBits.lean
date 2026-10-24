import CurrentAdditive.BitPolynomialShift

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open Polynomial
open CurrentAdditive.FiniteFieldConstructor.TrialSearch

theorem monicBits_topBit (d tail : ℕ) (htail : tail < 2 ^ d) :
    (monicBits d tail).testBit d = true := by
  have hpow : 0 < 2 ^ d := pow_pos (by omega) _
  have hdiv : (2 ^ d + tail) / 2 ^ d = 1 := by
    rw [Nat.add_comm]
    simpa [Nat.add_mul_div_left, Nat.div_eq_of_lt htail] using
      (Nat.add_mul_div_left tail 1 (2 ^ d))
  simp [monicBits, Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]

theorem monicBits_lt (d tail : ℕ) (htail : tail < 2 ^ d) :
    monicBits d tail < 2 ^ (d + 1) := by
  simp only [monicBits, pow_succ]
  omega

theorem monicBits_monic (d tail : ℕ) (htail : tail < 2 ^ d) :
    (polynomial (d + 1) (monicBits d tail)).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one d
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [coeff_polynomial]
    simp [show ¬ j < d + 1 by omega]
  · rw [coeff_polynomial]
    simp [monicBits_topBit d tail htail]

theorem monicBits_degree (d tail : ℕ) (htail : tail < 2 ^ d) :
    (polynomial (d + 1) (monicBits d tail)).natDegree = d := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [coeff_polynomial]
    simp [show ¬ j < d + 1 by omega]
  · rw [coeff_polynomial]
    simp [monicBits_topBit d tail htail]

#print axioms monicBits_monic
#print axioms monicBits_degree

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
