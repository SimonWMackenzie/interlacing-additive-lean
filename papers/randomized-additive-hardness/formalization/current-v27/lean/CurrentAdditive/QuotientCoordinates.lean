import CurrentAdditive.QuotientFieldSize

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open Polynomial

theorem powerBasis_coord_of_degree_lt (f p : Polynomial (ZMod 2))
    (hf : f.Monic) (hp : p.degree < f.degree) (i : Fin f.natDegree) :
    (AdjoinRoot.powerBasisAux' hf).repr (AdjoinRoot.mk f p) i = p.coeff i := by
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun,
    AdjoinRoot.modByMonicHom_mk,
    (Polynomial.modByMonic_eq_self_iff hf).mpr hp]

theorem quotient_coord (d modulus code : ℕ)
    (hmonic : (polynomial (d + 1) modulus).Monic)
    (hdegree : (polynomial (d + 1) modulus).natDegree = d)
    (i : Fin (polynomial (d + 1) modulus).natDegree) :
    (AdjoinRoot.powerBasisAux' hmonic).repr
        (AdjoinRoot.mk (polynomial (d + 1) modulus) (polynomial d code)) i =
      (if code.testBit i then (1 : ZMod 2) else 0) := by
  let f := polynomial (d + 1) modulus
  have hpdeg : (polynomial d code).degree < f.degree := by
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdegree]
    exact polynomial_degree_lt d code
  have hcoord := powerBasis_coord_of_degree_lt f (polynomial d code)
    hmonic hpdeg i
  have hi : (i : ℕ) < d := lt_of_lt_of_eq i.isLt hdegree
  simpa only [coeff_polynomial, hi, ↓reduceIte] using hcoord

#print axioms quotient_coord

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
