import CurrentAdditive.V42NearFullMargins

/-! The sufficient cutoff depends only on the fixed graph-promise constants,
not the actual edge/vertex counts or actual vertex-deletion tolerance. -/

namespace CurrentAdditive.V42Schedule

theorem sourceAllowance_mono (δ₁ δ₂ ζ : ℚ) (hδ : δ₁ ≤ δ₂) :
    sourceAllowance δ₁ ζ ≤ sourceAllowance δ₂ ζ := by
  unfold sourceAllowance
  gcongr

theorem commonCutoff_antitone (δ₁ δ₂ ζ : ℚ) (Δ : ℕ)
    (hδ₁ : 0 < δ₁) (hζ : 0 < ζ) (hδ : δ₁ ≤ δ₂) :
    commonCutoff δ₂ ζ Δ ≤ commonCutoff δ₁ ζ Δ := by
  have ha := sourceAllowance_mono δ₁ δ₂ ζ hδ
  have hap := sourceAllowance_pos δ₁ ζ hδ₁ hζ
  have hinv : 1/sourceAllowance δ₂ ζ ≤ 1/sourceAllowance δ₁ ζ :=
    one_div_le_one_div_of_le hap ha
  have hceil := Nat.ceil_mono hinv
  unfold commonCutoff
  omega

def fixedPromiseCutoff (γ : ℚ) (Δ : ℕ) : ℕ :=
  commonCutoff (γ/(4*Δ)) (γ/24) Δ

theorem fixedPromiseCutoff_controls (γ δv : ℚ) (Δ k : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hδ : γ/(4*Δ) ≤ δv)
    (hk : fixedPromiseCutoff γ Δ ≤ k) :
    commonCutoff δv (γ/24) Δ ≤ k := by
  have hΔq : (0:ℚ) < Δ := by exact_mod_cast hΔ
  have hδ0 : (0:ℚ) < γ/(4*Δ) := by positivity
  exact (commonCutoff_antitone _ _ _ Δ hδ0 (by positivity) hδ).trans hk

theorem fixedPromiseCutoff_ge (γ : ℚ) (Δ : ℕ) :
    200 ≤ fixedPromiseCutoff γ Δ ∧ 2*Δ ≤ fixedPromiseCutoff γ Δ := by
  unfold fixedPromiseCutoff commonCutoff
  omega

theorem fixedPromiseCutoff_graph (γ : ℚ) (Δ n m k : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hnm : n ≤ 2*m)
    (hk : fixedPromiseCutoff γ Δ ≤ k) :
    commonCutoff (V38Schedule.sourceDeltaV γ Δ n m) (γ/24) Δ ≤ k :=
  fixedPromiseCutoff_controls γ _ Δ k hγ hΔ
    (V39PublicSchedule.sourceDeltaV_lower γ Δ n m hγ hΔ hn hnm) hk

theorem dominant_margin_strict (k b : ℕ) (hk : 8 ≤ k) (hb : 4*k ≤ b) :
    (998/1000:ℚ) < 999/1000-2*((s k-1:ℕ):ℚ)*x b := by
  have hsx := (scalar_smallness k b hk hb).2.2.2.1
  have hs : 1 ≤ s k := by exact Nat.succ_le_of_lt (s_pos k)
  have hsub : ((s k-1:ℕ):ℚ)=(s k:ℚ)-1 := by
    rw [Nat.cast_sub hs,Nat.cast_one]
  have hx : 0 < x b := by unfold x; positivity
  rw [hsub]
  nlinarith only [hsx,hx]

#print axioms fixedPromiseCutoff_controls
#print axioms fixedPromiseCutoff_graph
#print axioms dominant_margin_strict

end CurrentAdditive.V42Schedule
