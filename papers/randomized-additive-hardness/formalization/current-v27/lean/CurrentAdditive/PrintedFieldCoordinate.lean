import CurrentAdditive.FieldConcreteBasis

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open CurrentAdditive.FiniteFieldConstructor.BitPrinter

theorem printed_bit_eq_field_dot (d modulus n : ℕ)
    (hd : 0 < d)
    (hmodulus : modulus < 2 ^ (d + 1))
    (htop : modulus.testBit d = true)
    (hmonic : (polynomial (d + 1) modulus).Monic)
    (hdegree : (polynomial (d + 1) modulus).natDegree = d)
    [Fact (Irreducible (polynomial (d + 1) modulus))]
    (x y : Fin (2 ^ d)) (j : Fin n) :
    bit d modulus x y j =
      decide ((∑ i : Fin d,
        xBits d x i *
          (fieldBasis d modulus hmonic hdegree).equivFun
            ((AdjoinRoot.mk (polynomial (d + 1) modulus)
              (polynomial d y)) ^ (j : ℕ)) i) = 1) := by
  have hpow := power_quotient d modulus y j hd hmodulus htop y.isLt
  rw [← hpow]
  simp_rw [fieldBasis_coord d modulus (power d modulus y j) hmonic hdegree]
  simpa only [xBits, bit] using dot_eq_decide d x (power d modulus y j)

#print axioms printed_bit_eq_field_dot

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
