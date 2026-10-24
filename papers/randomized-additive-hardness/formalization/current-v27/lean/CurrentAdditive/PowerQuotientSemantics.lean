import CurrentAdditive.QuotientMulSemantics

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open Polynomial CurrentAdditive.FiniteFieldConstructor.BitPrinter

theorem power_lt (d modulus y j : ℕ) (hd : 0 < d)
    (hmodulus : modulus < 2 ^ (d + 1))
    (htop : modulus.testBit d = true) (hy : y < 2 ^ d) :
    power d modulus y j < 2 ^ d := by
  induction j with
  | zero =>
      simpa only [power] using Nat.one_lt_two_pow (by omega : d ≠ 0)
  | succ j ih =>
      simpa only [power] using mul_lt d modulus (power d modulus y j) y
        hmodulus htop hy

theorem polynomial_one (d : ℕ) (hd : 0 < d) :
    polynomial d 1 = 1 := by
  have h := polynomial_extend 1 d 1 (by decide) (by omega)
  rw [h]
  norm_num [polynomial]

theorem power_quotient (d modulus y j : ℕ) (hd : 0 < d)
    (hmodulus : modulus < 2 ^ (d + 1))
    (htop : modulus.testBit d = true) (hy : y < 2 ^ d) :
    AdjoinRoot.mk (polynomial (d + 1) modulus)
        (polynomial d (power d modulus y j)) =
      (AdjoinRoot.mk (polynomial (d + 1) modulus) (polynomial d y)) ^ j := by
  induction j with
  | zero => simp [power, polynomial_one d hd]
  | succ j ih =>
      rw [power, mul_quotient d modulus (power d modulus y j) y hd
        hmodulus htop hy, ih, pow_succ]

#print axioms power_lt
#print axioms polynomial_one
#print axioms power_quotient

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
