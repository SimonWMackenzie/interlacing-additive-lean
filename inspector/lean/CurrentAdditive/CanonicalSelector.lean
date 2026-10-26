import CurrentAdditive.SmallBiasEncodedTable

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open CurrentAdditive.SmallBias

/-- A computable base-`H` enumeration of every selector tuple. The
coordinate at `i` is the `i`th base-`H` digit of its label. -/
def selector (q H : ℕ) : Fin (H ^ q) → Fin q → Fin H :=
  finFunctionFinEquiv.symm

theorem selector_bijective (q H : ℕ) : Function.Bijective (selector q H) :=
  finFunctionFinEquiv.symm.bijective

/-- The original finite theorem chose an arbitrary ordering of the same
tuples. This relabels computable positions to those semantic labels. -/
noncomputable def selectorRelabel (q H : ℕ) :
    Fin (H ^ q) ≃ Fin (Fintype.card (Fin q → Fin H)) :=
  finFunctionFinEquiv.symm.trans (Fintype.equivFin (Fin q → Fin H))

theorem fullSelector_relabel (q H : ℕ) (u : Fin (H ^ q)) :
    fullSelector q H (selectorRelabel q H u) = selector q H u := by
  simp [selectorRelabel, fullSelector, selector]

#print axioms selector_bijective
#print axioms fullSelector_relabel

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
