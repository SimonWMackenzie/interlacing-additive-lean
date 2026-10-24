import CurrentAdditive.ExplicitSeedLabels

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open Polynomial

noncomputable def fieldCoordEquiv (d modulus : ℕ)
    [Fact (Irreducible (polynomial (d + 1) modulus))]
    (hmonic : (polynomial (d + 1) modulus).Monic)
    (hdegree : (polynomial (d + 1) modulus).natDegree = d) :
    QuotientField d modulus ≃ₗ[ZMod 2] (Fin d → ZMod 2) :=
  (AdjoinRoot.powerBasisAux' hmonic).equivFun.trans
    (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finCongr hdegree.symm))

noncomputable def fieldBasis (d modulus : ℕ)
    [Fact (Irreducible (polynomial (d + 1) modulus))]
    (hmonic : (polynomial (d + 1) modulus).Monic)
    (hdegree : (polynomial (d + 1) modulus).natDegree = d) :
    Module.Basis (Fin d) (ZMod 2) (QuotientField d modulus) :=
  Module.Basis.ofEquivFun (fieldCoordEquiv d modulus hmonic hdegree)

theorem fieldBasis_coord (d modulus code : ℕ)
    [Fact (Irreducible (polynomial (d + 1) modulus))]
    (hmonic : (polynomial (d + 1) modulus).Monic)
    (hdegree : (polynomial (d + 1) modulus).natDegree = d)
    (i : Fin d) :
    (fieldBasis d modulus hmonic hdegree).equivFun
        (AdjoinRoot.mk (polynomial (d + 1) modulus) (polynomial d code)) i =
      (if code.testBit i then (1 : ZMod 2) else 0) := by
  simp only [fieldBasis, Module.Basis.equivFun_ofEquivFun,
    fieldCoordEquiv, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply]
  let f := polynomial (d + 1) modulus
  have hpdeg : (polynomial d code).degree < f.degree := by
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdegree]
    exact polynomial_degree_lt d code
  have hcoord := powerBasis_coord_of_degree_lt f (polynomial d code)
    hmonic hpdeg (finCongr hdegree.symm i)
  have hi : ((finCongr hdegree.symm i : Fin f.natDegree) : ℕ) < d :=
    lt_of_lt_of_eq (finCongr hdegree.symm i).isLt hdegree
  simpa only [coeff_polynomial, hi, ↓reduceIte] using hcoord

#print axioms fieldBasis_coord

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
