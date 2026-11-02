import CurrentAdditive.V42FixedPromiseCutoff

/-! Literal middle-column to required-allowance comparisons in replacement
v42 eq:width-margins. This closes the displayed chain independently of the
separately proved actual-quantity estimates and earlier sufficient guards. -/

namespace CurrentAdditive.V42NumericAllowances
noncomputable section
open V42Schedule

set_option maxRecDepth 10000

private theorem cast_le {a b:ℚ} (h:a ≤ b) : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast h

theorem dyadic_rpow (k : ℕ) (a : ℝ) :
    (s k:ℝ)^a=(2:ℝ)^((k:ℝ)*a) := by
  have hs : (s k:ℝ)=(2:ℝ)^(k:ℝ) := by simp [s,Real.rpow_natCast]
  rw [hs,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]

theorem scaled_dyadic_le (k c : ℕ) (a d : ℝ)
    (h : (c:ℝ)+(k:ℝ)*a ≤ d) :
    (2:ℝ)^c*(s k:ℝ)^a ≤ (2:ℝ)^d := by
  rw [dyadic_rpow,←Real.rpow_natCast (2:ℝ) c,
    ←Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h

theorem negative_power_le (k : ℕ) (a d : ℝ) (h : (k:ℝ)*a ≤ d) :
    (s k:ℝ)^a ≤ (2:ℝ)^d := by
  rw [dyadic_rpow]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h

theorem inverse_s (k : ℕ) : (s k:ℝ)^(-(1:ℝ))=((1/2^k:ℚ):ℝ) := by
  simp [Real.rpow_neg_one,s]

theorem sourceAllowance_real (δv ζ : ℚ) :
    (sourceAllowance δv ζ:ℝ)=(2:ℝ)^(-(16:ℝ))*
      min 1 (min (δv:ℝ) ((1/256:ℝ)*(ζ:ℝ))) := by
  unfold sourceAllowance
  push_cast
  norm_num [Real.rpow_neg]
  congr 1
  ring

theorem C128_bound : (V38Schedule.C128:ℝ) ≤ (2:ℝ)^(2176:ℕ) := by
  have hbase : (2^14:ℝ)/((255/256:ℝ)-1/2)^2 ≤ 2^17 := by norm_num
  have hC := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (2^14:ℝ)/((255/256:ℝ)-1/2)^2) hbase 128
  have heq : (V38Schedule.C128:ℝ)=((2^14:ℝ)/((255/256:ℝ)-1/2)^2)^128 := by
    unfold V38Schedule.C128
    push_cast
    rfl
  rw [heq]
  rw [←pow_mul] at hC
  exact hC

theorem middle_allowances (δv ζ : ℚ) (Δ k : ℕ)
    (hδ : 0 < δv) (hζ : 0 < ζ) (hk : commonCutoff δv ζ Δ ≤ k) :
    (s k:ℝ)^(-(1:ℝ)) ≤ (2:ℝ)^(-(16:ℝ))*
      min 1 (min (δv:ℝ) ((1/256:ℝ)*(ζ:ℝ))) ∧
    2*(Δ:ℝ)/(s k:ℝ) ≤ 1 ∧
    (s k:ℝ)^(-(2:ℝ)) ≤ 1/4 ∧
    (s k:ℝ)^(-(4:ℝ)) ≤ (ζ:ℝ)/128 ∧
    (s k:ℝ)^(-(24:ℝ)) ≤ 1/10000 ∧
    (s k:ℝ)^(-(14:ℝ)) ≤ 1/(32*(255/256:ℝ)) ∧
    (s k:ℝ)^(-(10:ℝ)) ≤ 1 ∧
    (s k:ℝ)^(-(16:ℝ)) ≤ 1/(128*(1/256:ℝ)) ∧
    (2:ℝ)^85*(s k:ℝ)^(-(53:ℝ)/8) ≤ 1 ∧
    512*(V38Schedule.C128:ℝ)*(s k:ℝ)^(-(104:ℝ)) ≤ 1/4 ∧
    (2:ℝ)^89*(s k:ℝ)^(-(5:ℝ)/8) ≤ 1/16 := by
  obtain ⟨hk200,hΔ,hfirst,hlast⟩:=cutoff_small δv ζ Δ k hδ hζ hk
  have hkR : (200:ℝ) ≤ k := by exact_mod_cast hk200
  have hsp : (0:ℝ) < s k := by exact_mod_cast s_pos k
  have hsp1 : (1:ℝ) ≤ s k := by exact_mod_cast (Nat.succ_le_of_lt (s_pos k))
  have hsΔ : 2*Δ ≤ s k := hΔ.trans (V38Cutoff.coefficient_le_power k)
  have hΔR : 2*(Δ:ℝ) ≤ s k := by exact_mod_cast hsΔ
  have hfirstR : (s k:ℝ)^(-(1:ℝ)) ≤ (sourceAllowance δv ζ:ℝ) := by
    rw [inverse_s]
    exact cast_le hfirst
  have hlastR : (s k:ℝ)^(-(1:ℝ)) ≤ (ζ:ℝ)/128 := by
    rw [inverse_s]
    simpa only [Rat.cast_div,Rat.cast_ofNat] using cast_le hlast
  refine ⟨by simpa only [sourceAllowance_real] using hfirstR,(div_le_one hsp).2 hΔR,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hh:=negative_power_le k (-2) (-2) (by nlinarith)
    rw [show (2:ℝ)^(-(2:ℝ))=1/4 by norm_num [Real.rpow_neg]] at hh
    exact hh
  · exact (Real.rpow_le_rpow_of_exponent_le hsp1 (by norm_num : -(4:ℝ) ≤ -1)).trans hlastR
  · have hh:=negative_power_le k (-24) (-14) (by nlinarith)
    rw [show (2:ℝ)^(-(14:ℝ))=1/16384 by norm_num [Real.rpow_neg]] at hh
    exact hh.trans (show (1/16384:ℝ) ≤ 1/10000 by norm_num)
  · have hh:=negative_power_le k (-14) (-5) (by nlinarith)
    rw [show (2:ℝ)^(-(5:ℝ))=1/32 by norm_num [Real.rpow_neg]] at hh
    exact hh.trans (show (1/32:ℝ) ≤ 1/(32*(255/256:ℝ)) by norm_num)
  · exact Real.rpow_le_one_of_one_le_of_nonpos hsp1 (by norm_num)
  · have hh:=Real.rpow_le_one_of_one_le_of_nonpos hsp1 (by norm_num : -(16:ℝ) ≤ 0)
    exact hh.trans (show (1:ℝ) ≤ 1/(128*(1/256:ℝ)) by norm_num)
  · have hh:=scaled_dyadic_le k 85 (-(53:ℝ)/8) 0 (by nlinarith)
    simpa using hh
  · have hp : 0 ≤ (s k:ℝ)^(-(104:ℝ)) := Real.rpow_nonneg hsp.le _
    have hmul:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left C128_bound (by norm_num : (0:ℝ) ≤ 512)) hp
    have heq : (512:ℝ)*(2:ℝ)^2176=(2:ℝ)^(2185:ℕ) := by
      rw [show (512:ℝ)=(2:ℝ)^9 by norm_num]
      rw [←pow_add]
    rw [heq] at hmul
    have hh:=scaled_dyadic_le k 2185 (-104) (-2) (by norm_num only [Nat.cast_ofNat]; nlinarith only [hkR])
    rw [show (2:ℝ)^(-(2:ℝ))=1/4 by norm_num [Real.rpow_neg]] at hh
    exact hmul.trans hh
  · have hh:=scaled_dyadic_le k 89 (-(5:ℝ)/8) (-4) (by nlinarith)
    rw [show (2:ℝ)^(-(4:ℝ))=1/16 by norm_num [Real.rpow_neg]] at hh
    exact hh

#print axioms middle_allowances

end
end CurrentAdditive.V42NumericAllowances
