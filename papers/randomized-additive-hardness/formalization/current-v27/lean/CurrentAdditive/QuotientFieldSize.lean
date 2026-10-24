import CurrentAdditive.PowerQuotientSemantics

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open Polynomial

abbrev QuotientField (d modulus : ℕ) :=
  AdjoinRoot (polynomial (d + 1) modulus)

@[reducible] noncomputable def quotientField (d modulus : ℕ)
    (hirr : Irreducible (polynomial (d + 1) modulus)) :
    Field (QuotientField d modulus) := by
  letI : Fact (Irreducible (polynomial (d + 1) modulus)) := ⟨hirr⟩
  infer_instance

noncomputable def quotientBasis (d modulus : ℕ)
    (hmonic : (polynomial (d + 1) modulus).Monic)
    (hdegree : (polynomial (d + 1) modulus).natDegree = d) :
    Module.Basis (Fin d) (ZMod 2) (QuotientField d modulus) := by
  simpa only [hdegree] using
    (AdjoinRoot.powerBasisAux' hmonic)

@[reducible] noncomputable def quotientFintype (d modulus : ℕ)
    (hmonic : (polynomial (d + 1) modulus).Monic)
    (hdegree : (polynomial (d + 1) modulus).natDegree = d) :
    Fintype (QuotientField d modulus) :=
  Fintype.ofEquiv (Fin d → ZMod 2)
    (quotientBasis d modulus hmonic hdegree).equivFun.toEquiv.symm

theorem quotient_card (d modulus : ℕ)
    (hmonic : (polynomial (d + 1) modulus).Monic)
    (hdegree : (polynomial (d + 1) modulus).natDegree = d) :
    @Fintype.card (QuotientField d modulus)
      (quotientFintype d modulus hmonic hdegree) = 2 ^ d := by
  classical
  letI := quotientFintype d modulus hmonic hdegree
  rw [Fintype.card_congr
    (quotientBasis d modulus hmonic hdegree).equivFun.toEquiv]
  simp [ZMod.card]

#print axioms quotient_card

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
