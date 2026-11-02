import CurrentAdditive.V39IncomingGuard

/-! The v42 weighted incoming proof uses the real diagonal density as its
moment parameter. The same explicit source constant controls that ratio. -/

namespace CurrentAdditive.V42IncomingGuard

noncomputable abbrev flagConstant : ℝ := V39IncomingGuard.flagConstant

theorem weighted_ratio_eq (W : ℝ) (hW : 0 < W) :
    (((2 : ℝ)^14*W)^128) / ((((255/256 : ℝ)-1/2)*W)^256) =
      flagConstant/W^128 := by
  let c : ℝ := (255/256 : ℝ)-1/2
  have hc : 0 < c := by norm_num [c]
  have hcne : c ≠ 0 := ne_of_gt hc
  have hWne : W ≠ 0 := ne_of_gt hW
  change ((2 : ℝ)^14*W)^128 / (c*W)^256 =
    (((2 : ℝ)^14/c^2)^128)/W^128
  field_simp

theorem destination_guard (s κ : ℕ) (θ : ℝ) (hs : 0 < s) (hκ : 1 ≤ κ)
    (hsource : flagConstant/(s : ℝ)^128 ≤ θ/4) :
    ∀ W : ℝ, 512*(s : ℝ)*κ ≤ W →
      (((2 : ℝ)^14*W)^128) / ((((255/256 : ℝ)-1/2)*W)^256) ≤ θ/4 := by
  intro W hW
  have hκR : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsW : (s : ℝ) ≤ W := by nlinarith
  rw [weighted_ratio_eq W (lt_of_lt_of_le hsR hsW)]
  have hconst : 0 ≤ flagConstant := by
    unfold flagConstant V39IncomingGuard.flagConstant
    positivity
  exact (div_le_div_of_nonneg_left hconst (by positivity)
    (pow_le_pow_left₀ hsR.le hsW 128)).trans hsource

end CurrentAdditive.V42IncomingGuard

#print axioms CurrentAdditive.V42IncomingGuard.weighted_ratio_eq
#print axioms CurrentAdditive.V42IncomingGuard.destination_guard


