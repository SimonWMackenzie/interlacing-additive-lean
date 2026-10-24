import CurrentAdditive.BitPolynomialExtend

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open Polynomial

theorem xor_lt_pow {a b width : ℕ} (ha : a < 2 ^ width)
    (hb : b < 2 ^ width) : Nat.xor a b < 2 ^ width := by
  change (a ^^^ b) < 2 ^ width
  exact Nat.bitwise_lt_two_pow ha hb

theorem shifted_divisor_lt (d e i divisor : ℕ)
    (hi : e + i ≤ d) (hdivisor : divisor < 2 ^ (e + 1)) :
    divisor <<< i < 2 ^ (d + 1) := by
  have hshift := Nat.shiftLeft_lt (m := i) hdivisor
  have hp : 2 ^ (e + 1 + i) ≤ 2 ^ (d + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  exact hshift.trans_le hp

theorem divisionStep_lt (d e i divisor acc : ℕ)
    (hi : e + i ≤ d) (hdivisor : divisor < 2 ^ (e + 1))
    (hacc : acc < 2 ^ (d + 1)) :
    (if acc.testBit (e + i) then Nat.xor acc (divisor <<< i) else acc) <
      2 ^ (d + 1) := by
  split_ifs
  · exact xor_lt_pow hacc (shifted_divisor_lt d e i divisor hi hdivisor)
  · exact hacc

theorem shifted_divisor_polynomial (d e i divisor : ℕ)
    (hi : e + i ≤ d) (hdivisor : divisor < 2 ^ (e + 1)) :
    polynomial (d + 1) (divisor <<< i) =
      X ^ i * polynomial (e + 1) divisor := by
  rw [polynomial_shift (d + 1) divisor i (by omega)]
  rw [polynomial_extend (e + 1) (d + 1 - i) divisor hdivisor (by omega)]

theorem divisionStep_polynomial (d e i divisor acc : ℕ)
    (hi : e + i ≤ d) (hdivisor : divisor < 2 ^ (e + 1)) :
    polynomial (d + 1)
      (if acc.testBit (e + i) then Nat.xor acc (divisor <<< i) else acc) =
    polynomial (d + 1) acc +
      (if acc.testBit (e + i) then
        X ^ i * polynomial (e + 1) divisor else 0) := by
  split_ifs with hbit
  · rw [polynomial_xor, shifted_divisor_polynomial d e i divisor hi hdivisor]
  · simp

#print axioms xor_lt_pow
#print axioms divisionStep_lt
#print axioms divisionStep_polynomial

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
