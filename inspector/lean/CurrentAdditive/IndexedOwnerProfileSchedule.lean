import CurrentAdditive.IndexedOwnerFixedEReceipt
import CurrentAdditive.IndexedProfileSchedule

/-! The owner initializer's original Nref profile is a direct component of
the checked generated-source schedule, on the very same indexed source. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicParameters

theorem indexed_owner_Nref_profile_at_parameters
    {G V Aux X Y : Type*}
    [Fintype G] [Fintype V] [Fintype Aux]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (L : ℕ) (hL : 2004 ≤ L)
    [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) μX μY)
    (μI : PositiveRationalLaw (G × (V ⊕ Aux)))
    (R : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin (q₂ L) → Option (Fin (s L)))
    (ξ₀ : Paper2.SourceMatrix.Tail (s L) Y)
    (d : ℕ) (hd : 3 ≤ d)
    (hD : D R = d)
    (hp : RestrictionProfile R μX.toFiniteLaw μY.toFiniteLaw
      (ρ L : ℝ) (d : ℤ)) :
    RestrictionProfile (Nref src R activity ξ₀)
      (ordinaryLaw src).toFiniteLaw (rowLaw src μI).toFiniteLaw
      (x L : ℝ) ((d+(L+3)/4+4*L+(L+3)/4 : ℕ) : ℤ) := by
  exact (generated_profiles_at_parameters L hL src μI R activity ξ₀
    d hd hD hp).2.2.2.2

#print axioms indexed_owner_Nref_profile_at_parameters

end CurrentAdditive.DeterministicIndexedMatrix.Sources
