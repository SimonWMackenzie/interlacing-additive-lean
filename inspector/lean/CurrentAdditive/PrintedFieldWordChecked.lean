import CurrentAdditive.FieldConcreteBasis
import CurrentAdditive.SmallBiasGenericBitBridge

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open CurrentAdditive.FiniteFieldConstructor.BitPrinter

theorem printed_bit_eq_vectorWord (d modulus n : ℕ)
    (hd : 0 < d)
    (hmodulus : modulus < 2 ^ (d + 1))
    (htop : modulus.testBit d = true)
    (hmonic : (polynomial (d + 1) modulus).Monic)
    (hdegree : (polynomial (d + 1) modulus).natDegree = d)
    [Fact (Irreducible (polynomial (d + 1) modulus))]
    (x y : Fin (2 ^ d)) (j : Fin n) :
    bit d modulus x y j =
      CurrentAdditive.FiniteFieldAdapter.vectorWord
        (fieldBasis d modulus hmonic hdegree)
        (xDecode d x, quotientCodeEquiv d modulus hmonic hdegree y) j := by
  have hpow := power_quotient d modulus y j hd hmodulus htop y.isLt
  have hcoord (i : Fin d) :
      (fieldBasis d modulus hmonic hdegree).equivFun
        ((quotientCodeEquiv d modulus hmonic hdegree y) ^ (j : ℕ)) i =
        boolCoeff ((power d modulus y j).testBit i) := by
    change (fieldBasis d modulus hmonic hdegree).equivFun
      ((AdjoinRoot.mk (polynomial (d + 1) modulus)
        (polynomial d y)) ^ (j : ℕ)) i = _
    rw [← hpow]
    exact fieldBasis_coord d modulus (power d modulus y j) hmonic hdegree i
  calc
    bit d modulus x y j = dot d x (power d modulus y j) := rfl
    _ = CurrentAdditive.FiniteFieldAdapter.vectorWord
        (fieldBasis d modulus hmonic hdegree)
        (xBits d x, quotientCodeEquiv d modulus hmonic hdegree y) j :=
      CurrentAdditive.SmallBias.dot_eq_vectorWord_of_coords d n
        (fieldBasis d modulus hmonic hdegree) x
        (quotientCodeEquiv d modulus hmonic hdegree y)
        (power d modulus y j) j hcoord
    _ = CurrentAdditive.FiniteFieldAdapter.vectorWord
        (fieldBasis d modulus hmonic hdegree)
        (xDecode d x, quotientCodeEquiv d modulus hmonic hdegree y) j := rfl

#print axioms printed_bit_eq_vectorWord

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
