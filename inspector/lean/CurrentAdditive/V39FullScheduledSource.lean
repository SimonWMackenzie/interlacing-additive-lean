import CurrentAdditive.V39SourceProfiles
import CurrentAdditive.V39FullScheduleGuards

/-! The literal full schedule instantiates every numerical source-profile
guard. The remaining test premise is arithmetic and is supplied by the
separately owned eventual-cutoff theorem. No source profile is an input. -/

namespace CurrentAdditive.V39FullScheduledSource

open Workspace.Types.CommComplexity Paper2 V38Schedule
open Paper2.SourceMatrix
open CurrentAdditive.EdgeSourceMatrix CurrentAdditive.V38Matrix

variable {X Y V E : Type*} [Fintype X] [Fintype Y] [Fintype V] [Fintype E]
variable {q₁ q₂ s : ℕ}

theorem costs_and_profiles [Nonempty V] [NeZero q₁] [NeZero q₂] [NeZero s]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool)
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂=EdgeSource.sourceQ0 (Fin (4*s)) E*r)
    (ξ₀ : Tail s Y) (d : ℕ) (hd : 3 ≤ d)
    (c δv ζ : ℚ) (L m : ℕ)
    (hS : s=fullS L) (hQ₁ : q₁=fullQ₁ L) (hQ₂ : q₂=fullQ₂ L)
    (htests : CommonTests (fullInput c L) m δv ζ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R
      μ.toFiniteLaw ν.toFiniteLaw ((fullRho L : ℚ) : ℝ) (d : ℤ))
    (hD : D R=d) :
    let a := 16+ell L
    let b := L+2*a
    D (M₁ (q₁:=q₁) (s:=s) R)=d+a ∧
    D (T (q₁:=q₁) (q₂:=q₂) (s:=s) R)=d+a+b ∧
    V38RestrictionProfiles.TwoThresholdProfile
      (fun γ z => M₁ (q₁:=q₁) (s:=s) R z γ)
      (ν.iid (q₁+s+1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw
      ((fullX L : ℚ) : ℝ) ((d+a : ℕ) : ℤ) ∧
    V38RestrictionProfiles.TwoThresholdProfile (T (q₁:=q₁) (q₂:=q₂) (s:=s) R)
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw
      (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw
      ((fullX L : ℚ) : ℝ) ((d+a+b : ℕ) : ℤ) ∧
    V38RestrictionProfiles.TwoThresholdProfile
      (fun Z k => V38Matrix.matrix order edge (by omega : 3 ≤ s) r hq R ξ₀ (.inl Z) k)
      (SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw
      (columnLaw (q₁:=q₁) (q₂:=q₂) (s:=s) (V:=V) μ hs).toFiniteLaw
      ((fullX L : ℚ) : ℝ) ((d+a+b+a : ℕ) : ℤ) := by
  dsimp only
  subst s q₁ q₂
  obtain ⟨hi,ho,hr⟩ := V39FullScheduleGuards.full_source_guards c δv ζ L m htests
  have hx : ((fullX L : ℚ) : ℝ) ≤ 1 := by
    have hp : (1 : ℝ) ≤ (2 : ℝ)^(10*L) := one_le_pow₀ (by norm_num)
    simpa [fullX] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1) hp
  have hq₁ : fullQ₁ L+2=fullS L := by
    have hh := fullS_ge_256 L
    unfold fullQ₁
    omega
  have hq₂ : fullQ₂ L=2^(L+2*(16+ell L)) := by
    unfold fullQ₂ fullS
    rw [← pow_mul,← pow_add]
    congr 1
    omega
  exact V39SourceProfiles.costs_and_profiles μ ν R order edge hs r hq ξ₀ d
    (16+ell L) (L+2*(16+ell L)) hd
    ((fullRho L : ℚ) : ℝ) ((fullX L : ℚ) : ℝ) hx rfl hq₁ hq₂ hi ho hr hp hD

#print axioms costs_and_profiles

end CurrentAdditive.V39FullScheduledSource
