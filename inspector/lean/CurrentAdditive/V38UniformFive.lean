import CurrentAdditive.V38UniformThree
import CurrentAdditive.V39FiveBlocks

namespace Paper2.V38UniformSmallBlockAdapter

open Workspace.Types.CommComplexity

variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

/-- The current two-threshold profile gives the five-block high bound on
the actual finite uniform interlace. -/
theorem five_block_high_uniform (F : X → Y → Bool)
    (θ : ℝ) (H : ℕ) (hH : 2 ≤ H) (hθ : 0 < θ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F
      (FiniteLaw.uniform X) (FiniteLaw.uniform Y) θ (H : ℤ))
    (R : Finset (Fin 5 × X)) (K : Finset (Fin 5 → Y))
    (hmem : (R, K) ∈ NPCC.bracketGE X Y 5 ((2 : ℝ) ^ 3 * θ) (9 / 25 : ℝ)) :
    H + 3 ≤ D (NPCC.subgame (fullInterlace F 5) R K) := by
  obtain ⟨hrow, hcol⟩ := bracket_to_uniform_mass 5 ((2 : ℝ) ^ 3 * θ)
    (9 / 25 : ℝ) R K hmem
  have hν := rational_uniform_toFiniteLaw Y
  have h := V38SmallBlocks.five_block_high F (FiniteLaw.uniform X)
    (PositiveRationalLaw.uniform Y) θ H hH hθ
    (by simpa only [hν] using hp) (R : Set _) (K : Set _)
    (by norm_num at hrow ⊢; simpa using hrow) (by simpa only [hν] using hcol)
  rwa [finite_restrictionD_eq] at h

theorem five_block_C_of_profile (F : X → Y → Bool)
    (C : ℕ) (θ : ℝ) (hC : 3 ≤ C) (hθ : 0 < θ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F
      (FiniteLaw.uniform X) (FiniteLaw.uniform Y) θ ((C : ℤ) - 1))
    (R : Finset (Fin 5 × X)) (K : Finset (Fin 5 → Y))
    (hmem : (R, K) ∈ NPCC.bracketGE X Y 5 ((2 : ℝ) ^ 3 * θ) (9 / 25 : ℝ)) :
    C + 2 ≤ D (NPCC.subgame (fullInterlace F 5) R K) := by
  have hp' : V38RestrictionProfiles.TwoThresholdProfile F
      (FiniteLaw.uniform X) (FiniteLaw.uniform Y) θ ((C - 1 : ℕ) : ℤ) := by
    simpa only [Nat.cast_sub (by omega : 1 ≤ C), Nat.cast_one] using hp
  have h := five_block_high_uniform F θ (C - 1) (by omega) hθ hp' R K hmem
  omega

#print axioms five_block_high_uniform
#print axioms five_block_C_of_profile

end Paper2.V38UniformSmallBlockAdapter
