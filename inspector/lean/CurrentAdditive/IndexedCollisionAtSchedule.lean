import CurrentAdditive.GeneratedCollisionExact
import CurrentAdditive.DeterministicParameters

/-! The final extra-position clause of Appendix I `det:profiles`, on the
actual indexed gamma source at the manuscript's deterministic schedule. This
uses the exact eight-wise collision theorem and does not require the number of
selected head/tail coordinates to be at most the source's-wise parameter. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.SourceProjectionDiagonal
open Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicParameters

theorem indexed_collision_cost_at_parameters
    {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
    [DecidableEq X] [DecidableEq Y]
    (L : ℕ) (hL : 2004 ≤ L)
    [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := 8192) (q₁ := q₁ L)
      (q₂ := q₂ L) (s := s L) μX μY)
    (R : X → Y → Bool)
    (activity : I → Fin (q₂ L) → Option (Fin (s L)))
    (ξ₀ : Tail (s L) Y)
    (d : ℕ) (hd : 3 ≤ d)
    (hprofile : RestrictionProfile R μX.toFiniteLaw μY.toFiniteLaw
      (ρ L : ℝ) (d : ℤ))
    (bin : Fin (s L)) (α : Fin (q₂ L)) (K : Set src.inner.Label)
    (B : Fin 3 → Set X) (W : Set src.gamma.Label)
    (i₁ i₂ i₀ : I) (p p' : Fin (s L)) (hpp : p ≠ p')
    (h₁ : activity i₁ α = some p) (h₂ : activity i₂ α = some p')
    (h₀ : activity i₀ α = none)
    (U : Set (Column src)) (V : Set (Row (I := I) src))
    (hK : ∀ z ∈ K, Sum.inl (bin, z) ∈ V)
    (hB : ∀ t u, u ∈ B t →
      Sum.inr (collisionItem i₁ i₂ i₀ t, u) ∈ V)
    (hW : ∀ γ ∈ W, Column.diagonal (α, γ) ∈ U)
    (hhead : ∀ r, 2 * (s L : ℝ) * (ρ L : ℝ) ≤
      μX.toFiniteLaw.prob
        (fun u => (r, u) ∈ (fun z => src.inner.decode z α) '' K))
    (hsource : ∀ t, 2 * (s L : ℝ) * (ρ L : ℝ) ≤
      μX.toFiniteLaw.prob (· ∈ B t))
    (hWmass : (1/2 : ℝ) < src.gamma.law.toFiniteLaw.prob (· ∈ W)) :
    d + (L+3)/4 + 1 ≤
      Paper2.Compression.restrictionD (N src R activity ξ₀) U V := by
  have hρ : (0 : ℝ) < (ρ L : ℝ) := by
    unfold ρ
    have hN := N_pos L
    positivity
  have hs : s L = 2^((L+3)/4) := rfl
  have hq : q₁ L + 3 = s L + 1 := by
    have hlarge := s_ge_64 L (by omega)
    dsimp [q₁]
    omega
  have hsmallQ : (s L : ℚ) * ρ L ≤ 1/1000 := s_rho_small L hL
  have hsmall : (s L : ℝ) * (ρ L : ℝ) ≤ 1/1000 := by
    have hh : ((((s L : ℚ) * ρ L : ℚ)) : ℝ) ≤ ((1/1000 : ℚ) : ℝ) := by
      exact_mod_cast hsmallQ
    simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_one, Rat.cast_ofNat] using hh
  have hscale : 2 * (s L : ℝ) * (ρ L : ℝ) ≤ 1 := by nlinarith
  exact indexed_collision_cost_exact src (by decide) R activity ξ₀
    d ((L+3)/4) (ρ L : ℝ) (by omega) (by omega) hρ
    hs hq hscale hprofile bin α K B W i₁ i₂ i₀ p p' hpp
    h₁ h₂ h₀ U V hK hB hW hhead hsource hWmass

end CurrentAdditive.DeterministicIndexedMatrix.Sources
