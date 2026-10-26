import CurrentAdditive.RawProductSemantics

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open Polynomial CurrentAdditive.FiniteFieldConstructor.BitPrinter

theorem reduce_polynomial_relation (d modulus p : ℕ) (hd : 0 < d)
    (hmodulus : modulus < 2 ^ (d + 1))
    (htop : modulus.testBit d = true) (hp : p < 2 ^ (2 * d)) :
    ∃ q : Polynomial (ZMod 2),
      polynomial d (reduce d modulus p) =
        polynomial (2 * d) p + polynomial (d + 1) modulus * q := by
  have hrun := run_relation (2 * d - 1) d modulus d p (by omega) hmodulus
  obtain ⟨q, hq⟩ := hrun
  refine ⟨q, ?_⟩
  have hout := reduce_lt d modulus p hmodulus htop hp
  have hext := polynomial_extend d (2 * d) (reduce d modulus p) hout (by omega)
  rw [reduce_eq_run] at hext ⊢
  have hq' : polynomial (2 * d) (run d modulus d p) =
      polynomial (2 * d) p + polynomial (d + 1) modulus * q := by
    simpa only [show (2 * d - 1) + 1 = 2 * d by omega] using hq
  exact hext.symm.trans hq'

theorem mul_polynomial_relation (d modulus a b : ℕ) (hd : 0 < d)
    (hmodulus : modulus < 2 ^ (d + 1))
    (htop : modulus.testBit d = true) (hb : b < 2 ^ d) :
    ∃ q : Polynomial (ZMod 2),
      polynomial d (mul d modulus a b) =
        polynomial d a * polynomial d b + polynomial (d + 1) modulus * q := by
  obtain ⟨q, hq⟩ := reduce_polynomial_relation d modulus (rawProduct d a b)
    hd hmodulus htop (rawProduct_lt d a b hb)
  refine ⟨q, ?_⟩
  simpa only [mul, rawProduct_polynomial d a b hb] using hq

theorem mul_quotient (d modulus a b : ℕ) (hd : 0 < d)
    (hmodulus : modulus < 2 ^ (d + 1))
    (htop : modulus.testBit d = true) (hb : b < 2 ^ d) :
    AdjoinRoot.mk (polynomial (d + 1) modulus)
        (polynomial d (mul d modulus a b)) =
      AdjoinRoot.mk (polynomial (d + 1) modulus) (polynomial d a) *
        AdjoinRoot.mk (polynomial (d + 1) modulus) (polynomial d b) := by
  obtain ⟨q, hq⟩ := mul_polynomial_relation d modulus a b hd hmodulus htop hb
  rw [hq]
  simp [map_add, map_mul, AdjoinRoot.mk_self]

#print axioms reduce_polynomial_relation
#print axioms mul_polynomial_relation
#print axioms mul_quotient

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
