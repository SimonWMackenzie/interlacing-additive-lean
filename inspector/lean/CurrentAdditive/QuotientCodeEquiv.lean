import CurrentAdditive.DotSemantics

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open Polynomial

noncomputable def quotientCharP (d modulus : ℕ)
    (hirr : Irreducible (polynomial (d + 1) modulus)) :
    CharP (QuotientField d modulus) 2 := by
  letI := quotientField d modulus hirr
  exact charP_of_injective_algebraMap' (ZMod 2) 2

theorem quotientCode_injective (d modulus : ℕ)
    (hmonic : (polynomial (d + 1) modulus).Monic)
    (hdegree : (polynomial (d + 1) modulus).natDegree = d) :
    Function.Injective (fun x : Fin (2 ^ d) =>
      AdjoinRoot.mk (polynomial (d + 1) modulus) (polynomial d x)) := by
  intro x y hxy
  apply lowEncoding_injective d
  apply Subtype.ext
  have hfdegree : (polynomial (d + 1) modulus).degree = d := by
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdegree]
  have hxdeg : (polynomial d x).degree <
      (polynomial (d + 1) modulus).degree := by
    rw [hfdegree]
    exact polynomial_degree_lt d x
  have hydeg : (polynomial d y).degree <
      (polynomial (d + 1) modulus).degree := by
    rw [hfdegree]
    exact polynomial_degree_lt d y
  have hmap := congrArg (AdjoinRoot.modByMonicHom hmonic) hxy
  simpa only [AdjoinRoot.modByMonicHom_mk,
    (Polynomial.modByMonic_eq_self_iff hmonic).mpr hxdeg,
    (Polynomial.modByMonic_eq_self_iff hmonic).mpr hydeg] using hmap

theorem quotientCode_surjective (d modulus : ℕ)
    (hmonic : (polynomial (d + 1) modulus).Monic)
    (hdegree : (polynomial (d + 1) modulus).natDegree = d) :
    Function.Surjective (fun x : Fin (2 ^ d) =>
      AdjoinRoot.mk (polynomial (d + 1) modulus) (polynomial d x)) := by
  letI := quotientFintype d modulus hmonic hdegree
  have hcard : Fintype.card (Fin (2 ^ d)) =
      Fintype.card (QuotientField d modulus) := by
    simpa [quotient_card d modulus hmonic hdegree] using
      (Fintype.card_fin (2 ^ d))
  let equiv : Fin (2 ^ d) ≃ QuotientField d modulus := Fintype.equivOfCardEq hcard
  exact (Finite.injective_iff_surjective_of_equiv equiv).mp
    (quotientCode_injective d modulus hmonic hdegree)

noncomputable def quotientCodeEquiv (d modulus : ℕ)
    (hmonic : (polynomial (d + 1) modulus).Monic)
    (hdegree : (polynomial (d + 1) modulus).natDegree = d) :
    Fin (2 ^ d) ≃ QuotientField d modulus :=
  Equiv.ofBijective _ ⟨quotientCode_injective d modulus hmonic hdegree,
    quotientCode_surjective d modulus hmonic hdegree⟩

#print axioms quotientCode_injective
#print axioms quotientCode_surjective
#print axioms quotientCodeEquiv

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
