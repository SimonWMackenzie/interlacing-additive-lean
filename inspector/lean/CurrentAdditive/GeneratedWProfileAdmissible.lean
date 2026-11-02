import CurrentAdditive.GeneratedWProfileAtSchedule

/-! The Appendix I admissibility record contains the two public numeric
guards needed for the literal generated internal weak profile. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicParameters

theorem generated_W_profile_of_admissible
    {G V Aux X Y : Type*} [Fintype G] [Fintype V] [Fintype Aux]
    [Fintype X] [Fintype Y] [DecidableEq G] [DecidableEq V]
    [DecidableEq Aux] [DecidableEq X] [DecidableEq Y]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (L Δ n m Caux : ℕ) (γ : ℚ) (hL : 2004 ≤ L)
    [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)] [NeZero (w L)]
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) μX μY)
    (μI : PositiveRationalLaw (G × (V ⊕ Aux)))
    (streams : InternalStreams src μI (w L))
    (R : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin (q₂ L) → Option (Fin (s L)))
    (ξ₀ : Tail (s L) Y) (d : ℕ) (hd : 3 ≤ d)
    (hD : D R = d)
    (hp : RestrictionProfile R μX.toFiniteLaw μY.toFiniteLaw
      (ρ L : ℝ) (d : ℤ))
    (hadm : Admissible L Δ n m Caux γ) :
    RestrictionProfile (W src streams R activity ξ₀)
      streams.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin (w L))).prod
        (columnLaw src)).toFiniteLaw)
      (θ L : ℝ)
      ((d+(L+3)/4+4*L+(L+3)/4+2*L : ℕ) : ℤ) := by
  have hx : (w L : ℝ) * (x L : ℝ) ≤ 1/10000 := by
    have hq := hadm.w_x
    have hr : (((w L : ℚ) * x L : ℚ) : ℝ) ≤
        ((1/10000 : ℚ) : ℝ) := Rat.cast_le.mpr hq
    simpa [Rat.cast_mul, Rat.cast_div] using hr
  exact generated_W_profile_at_schedule L hL src μI streams
    R activity ξ₀ d hd hD hp hadm.exception_theta hx

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.generated_W_profile_of_admissible
