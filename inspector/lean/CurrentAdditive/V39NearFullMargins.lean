import CurrentAdditive.V38Schedule
import Paper2.SourceSurvivingCollisionsItems

/-! Scalar read-back from the literal public full schedule to the exact
margins consumed by the actual source near-full theorem. -/

namespace CurrentAdditive.V39NearFullMargins

open Paper2 Paper2.SourceSurvivingCollisions V38Schedule

theorem full_eta_eq_deletionAllowance
    {V E : Type*} [Fintype V] [Fintype E]
    (γ : ℚ) (Δ L : ℕ) :
    ((fullEta (fullConstant γ Δ (Fintype.card V) (Fintype.card E)) L : ℚ) : ℝ) =
      deletionAllowance (V := V) (E := E) (γ : ℝ) Δ (fullS L) := by
  unfold fullEta fullConstant sourceDeltaV sourceZeta deletionAllowance
    vertexTolerance witnessDensity SourceDeletionParameters.eta
  norm_num only [Rat.cast_div,Rat.cast_mul,Rat.cast_min,Rat.cast_natCast,
    Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]
  rw [show ((γ : ℝ)/24)/256 = (1/256 : ℝ)*((γ : ℝ)/24) by ring]
  rw [min_assoc]

theorem numeric_margins (s q₁ q₂ : ℕ) (hs : 4 ≤ s) (hq : 0 < q₂)
    (δ ζ x : ℝ) (hδ : 0 < δ) (hζ : 0 < ζ) (hx : 0 < x)
    (hcount : 8*(s : ℝ)*q₁ ≤ ζ*q₂/16)
    (hsx : (s : ℝ)*x ≤ 1/10000) (hqx : (q₂ : ℝ)*x ≤ 1/10000) :
    let η := SourceDeletionParameters.eta s δ ζ
    0 < η ∧ η < 1/100 ∧ η*s/(255/256 : ℝ) ≤ 1/1000 ∧
    8*(s : ℝ)*q₁+1024*s*η*q₂ < ζ*q₂/4 ∧
    2*(q₂ : ℝ)*x ≤ 1/8 ∧ 2*(s : ℝ)*x < 999/1000 ∧
    (998/1000 : ℝ) ≤ 999/1000-2*((s-1 : ℕ) : ℝ)*x := by
  dsimp only
  have hη := SourceDeletionParameters.eta_pos s (by omega) δ ζ hδ hζ
  have hmass := SourceDeletionParameters.protected_mass_guards s hs δ ζ hδ hζ
  have hcoord := SourceDeletionParameters.coordinate_allowance s q₁ q₂
    (by omega) hq δ ζ hζ hcount
  refine ⟨hη,by linarith,hmass.1,hcoord,by linarith,by linarith,?_⟩
  have hsub : ((s-1 : ℕ) : ℝ) = (s : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ s),Nat.cast_one]
  rw [hsub]
  nlinarith

end CurrentAdditive.V39NearFullMargins

#print axioms CurrentAdditive.V39NearFullMargins.full_eta_eq_deletionAllowance
#print axioms CurrentAdditive.V39NearFullMargins.numeric_margins
