import CurrentAdditive.DeterministicIndexedHeadMarginals

/-! Each indexed head coordinate of M₁ inherits the base rectangle profile
under the actual Gamma-label law. This is the block input to the separate
counting/conditioning argument; it is not the whole M₁ profile. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2 Paper2.SourceMatrix

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

namespace Sources

theorem M₁_head_block_profile
    (R₀ : X → Y → Bool) (ρ : ℝ) (d : ℤ)
    (hD : 1 ≤ D)
    (hp : RestrictionProfile R₀ μX.toFiniteLaw μY.toFiniteLaw ρ d)
    (i : Fin q₁) :
    RestrictionProfile
      (fun u γ => M₁ src R₀ (i, u) γ)
      μX.toFiniteLaw src.gamma.law.toFiniteLaw ρ d := by
  intro j
  simpa only [M₁_entry] using
    (RestrictionLowerBound.pullback R₀
      μX.toFiniteLaw μY.toFiniteLaw
      μX.toFiniteLaw src.gamma.law.toFiniteLaw
      (fun u : X => u) (fun γ => head (gammaWord src γ) i)
      (by intro E; rfl) (gamma_head_pushes src hD i)
      ρ ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val)
      (d - (j.val : ℤ)) (hp j))

end Sources

end CurrentAdditive.DeterministicIndexedMatrix
