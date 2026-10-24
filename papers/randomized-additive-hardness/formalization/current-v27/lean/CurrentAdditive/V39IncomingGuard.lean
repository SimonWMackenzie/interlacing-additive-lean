import Mathlib

/-! The current scheduled flag constant supplies the sharper inherited
moment ratio used by the actual complete-stream section constructor. -/

namespace CurrentAdditive.V39IncomingGuard

noncomputable def flagConstant : ℝ :=
  ((2 : ℝ)^14 / ((255/256 : ℝ)-1/2)^2)^128

theorem flag_ratio_le (s m : ℕ) (hs : 0 < s) (hm : s ≤ m) :
    2*((64 : ℝ)*m)^128 / (((255/256 : ℝ)-1/2)*m)^256 ≤
      flagConstant/(s : ℝ)^128 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast lt_of_lt_of_le hs hm
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  let c : ℝ := (255/256 : ℝ)-1/2
  have hc : 0 < c := by norm_num [c]
  have hloose : 2*((64 : ℝ)*m)^128 ≤ ((2 : ℝ)^14*m)^128 := by
    have hbase : 0 ≤ 64*(m : ℝ) := by positivity
    have htwo : (2 : ℝ) ≤ 2^(128 : ℕ) := by norm_num
    calc
      _ ≤ 2^(128 : ℕ)*(64*(m : ℝ))^128 :=
        mul_le_mul_of_nonneg_right htwo (pow_nonneg hbase _)
      _ = (128*(m : ℝ))^128 := by rw [← mul_pow]; congr 1; ring
      _ ≤ _ := by gcongr; norm_num
  have heq : ((2 : ℝ)^14*m)^128 / (c*m)^256 = flagConstant/(m : ℝ)^128 := by
    have hcne : c ≠ 0 := ne_of_gt hc
    have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
    change ((2 : ℝ)^14*m)^128 / (c*m)^256 =
      (((2 : ℝ)^14/c^2)^128)/(m : ℝ)^128
    field_simp
  have hconst : 0 ≤ flagConstant := by unfold flagConstant; positivity
  calc
    _ ≤ ((2 : ℝ)^14*m)^128 / (c*m)^256 := by
      exact div_le_div_of_nonneg_right hloose (by positivity)
    _ = flagConstant/(m : ℝ)^128 := heq
    _ ≤ flagConstant/(s : ℝ)^128 := by
      apply div_le_div_of_nonneg_left hconst (by positivity)
      exact pow_le_pow_left₀ hspos.le (by exact_mod_cast hm) 128

/-- The source's C128*s^-128 bound implies every selected group's
required numerical guard, since every such group has at least s origins. -/
theorem source_guard (s : ℕ) (θ : ℝ) (hs : 0 < s)
    (hsource : flagConstant/(s : ℝ)^128 ≤ θ/4) :
    ∀ m : ℕ, s ≤ m →
      2*((64 : ℝ)*m)^128 / (((255/256 : ℝ)-1/2)*m)^256 ≤ θ/4 := by
  intro m hm
  exact (flag_ratio_le s m hs hm).trans hsource

theorem destination_guard (s κ : ℕ) (θ : ℝ) (hs : 0 < s) (hκ : 1 ≤ κ)
    (hsource : flagConstant/(s : ℝ)^128 ≤ θ/4) :
    ∀ m : ℕ, 256*(s : ℝ)*κ ≤ m →
      2*((64 : ℝ)*m)^128 / (((255/256 : ℝ)-1/2)*m)^256 ≤ θ/4 := by
  intro m hm
  apply source_guard s θ hs hsource m
  have hκ' : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hs' : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hsm : (s : ℝ) ≤ m := by nlinarith
  exact_mod_cast hsm

end CurrentAdditive.V39IncomingGuard

#print axioms CurrentAdditive.V39IncomingGuard.flagConstant
#print axioms CurrentAdditive.V39IncomingGuard.flag_ratio_le
#print axioms CurrentAdditive.V39IncomingGuard.source_guard
#print axioms CurrentAdditive.V39IncomingGuard.destination_guard
