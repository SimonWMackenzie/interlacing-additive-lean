import CurrentAdditive.ExplicitSeedLabels

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open CurrentAdditive.FiniteFieldConstructor.BitPrinter

theorem printed_bit_eq_quotient_dot (d modulus n : ℕ)
    (hd : 0 < d)
    (hmodulus : modulus < 2 ^ (d + 1))
    (htop : modulus.testBit d = true)
    (hmonic : (polynomial (d + 1) modulus).Monic)
    (hdegree : (polynomial (d + 1) modulus).natDegree = d)
    (x y : Fin (2 ^ d)) (j : Fin n) :
    bit d modulus x y j =
      decide ((∑ i : Fin d,
        xBits d x i *
          (concreteBasis d modulus hmonic hdegree).equivFun
            ((AdjoinRoot.mk (polynomial (d + 1) modulus)
              (polynomial d y)) ^ (j : ℕ)) i) = 1) := by
  have hpow := power_quotient d modulus y j hd hmodulus htop y.isLt
  rw [← hpow]
  have hcoord (i : Fin d) :
      (concreteBasis d modulus hmonic hdegree).equivFun
          (AdjoinRoot.mk (polynomial (d + 1) modulus)
            (polynomial d (power d modulus y j))) i =
        boolCoeff ((power d modulus y j).testBit i) := by
    exact concreteBasis_coord d modulus (power d modulus y j)
      hmonic hdegree i
  simp_rw [hcoord]
  simpa only [xBits, bit] using dot_eq_decide d x (power d modulus y j)

#print axioms printed_bit_eq_quotient_dot

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
