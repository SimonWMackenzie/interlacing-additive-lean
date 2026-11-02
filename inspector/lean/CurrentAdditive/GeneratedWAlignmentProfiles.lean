import CurrentAdditive.IndexedProfileSchedule

/-! The three source profiles consumed by the same generated W alignment
argument are components of one checked profile schedule. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicParameters

theorem indexed_alignment_source_profiles
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
    RestrictionProfile (A src R)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin (q₁ L))).prod μX).toFiniteLaw
      (x L : ℝ) ((d+(L+3)/4 : ℕ) : ℤ) ∧
    RestrictionProfile (T src R)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin (q₂ L))).prod
        src.gamma.law).toFiniteLaw
      (x L : ℝ) ((d+(L+3)/4+4*L : ℕ) : ℤ) ∧
    RestrictionProfile (Nref src R activity ξ₀)
      (ordinaryLaw src).toFiniteLaw (rowLaw src μI).toFiniteLaw
      (x L : ℝ) ((d+(L+3)/4+4*L+(L+3)/4 : ℕ) : ℤ) := by
  have h := generated_profiles_at_parameters L hL src μI R activity ξ₀
    d hd hD hp
  exact ⟨h.2.1, h.2.2.2.1, h.2.2.2.2⟩

#print axioms indexed_alignment_source_profiles

end CurrentAdditive.DeterministicIndexedMatrix.Sources
