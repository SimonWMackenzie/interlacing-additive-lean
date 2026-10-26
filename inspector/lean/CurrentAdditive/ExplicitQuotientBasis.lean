import CurrentAdditive.QuotientCodeEquiv

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open Polynomial

noncomputable def concreteCoordEquiv (d modulus : ℕ)
    (hmonic : (polynomial (d + 1) modulus).Monic)
    (hdegree : (polynomial (d + 1) modulus).natDegree = d) :
    QuotientField d modulus ≃ₗ[ZMod 2] (Fin d → ZMod 2) :=
  (AdjoinRoot.powerBasisAux' hmonic).equivFun.trans
    (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finCongr hdegree.symm))

noncomputable def concreteBasis (d modulus : ℕ)
    (hmonic : (polynomial (d + 1) modulus).Monic)
    (hdegree : (polynomial (d + 1) modulus).natDegree = d) :
    Module.Basis (Fin d) (ZMod 2) (QuotientField d modulus) :=
  Module.Basis.ofEquivFun (concreteCoordEquiv d modulus hmonic hdegree)

theorem concreteBasis_coord (d modulus code : ℕ)
    (hmonic : (polynomial (d + 1) modulus).Monic)
    (hdegree : (polynomial (d + 1) modulus).natDegree = d)
    (i : Fin d) :
    (concreteBasis d modulus hmonic hdegree).equivFun
        (AdjoinRoot.mk (polynomial (d + 1) modulus) (polynomial d code)) i =
      (if code.testBit i then (1 : ZMod 2) else 0) := by
  simp only [concreteBasis, Module.Basis.equivFun_ofEquivFun,
    concreteCoordEquiv, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply]
  have h := quotient_coord d modulus code hmonic hdegree (finCongr hdegree.symm i)
  simpa [LinearMap.funLeft_apply] using h

#print axioms concreteBasis_coord

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
