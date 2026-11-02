import CurrentAdditive.V42Schedule

namespace CurrentAdditive.V42Schedule

open V39ExceptionBudget

def sourceAllowance (δv ζ : ℚ) : ℚ :=
  min 1 (min δv (ζ/256))/2^16

def commonCutoff (δv ζ : ℚ) (Δ : ℕ) : ℕ :=
  200 + 2*Δ + Nat.ceil (1/sourceAllowance δv ζ) + Nat.ceil (128/ζ)

theorem sourceAllowance_pos (δv ζ : ℚ) (hδ : 0 < δv) (hζ : 0 < ζ) :
    0 < sourceAllowance δv ζ := by unfold sourceAllowance; positivity

theorem cutoff_small (δv ζ : ℚ) (Δ k : ℕ)
    (hδ : 0 < δv) (hζ : 0 < ζ) (hk : commonCutoff δv ζ Δ  ≤  k) :
    200 ≤ k ∧ 2*Δ ≤ k ∧ (1:ℚ)/2^k  ≤  sourceAllowance δv ζ ∧
      (1:ℚ)/2^k  ≤  ζ/128 := by
  have hfirst := V39FullCutoff.inverse_bound (sourceAllowance δv ζ)
    (sourceAllowance_pos δv ζ hδ hζ)
  have hlast := V39FullCutoff.inverse_bound (ζ/128) (by positivity)
  have heq : (1:ℚ)/(ζ/128)=128/ζ := by ring
  unfold V39FullCutoff.inverseExponent at hfirst hlast
  rw [heq] at hlast
  unfold commonCutoff at hk
  refine ⟨by omega,by omega,?_,?_⟩
  · exact (reciprocal_le _ _ (by omega)).trans hfirst
  · exact (reciprocal_le _ _ (by omega)).trans hlast

theorem scalar_smallness (k b : ℕ) (hk : 8 ≤ k) (hb : 4*k ≤ b) :
    256 ≤ s k ∧ 4*(s k:ℚ)^2*rho b ≤ 1 ∧
    (q₂ k b:ℚ)*x b ≤ 1/10000 ∧ (s k:ℚ)*x b ≤ 1/10000 ∧
    (w k:ℚ)*x b ≤ 1/10000 ∧
    (w k:ℚ)^2*x b ≤ eta k/(32*(255/256:ℚ)) ∧
    (w k:ℚ)^2*q₂ k b*x b ≤ 1 ∧
    (w k:ℚ)*q₂ k b*x b ≤ eta k/(128*(1/256:ℚ)) := by
  have hsp : (s k:ℚ)=2^k := by simp [s]
  have hwp : (w k:ℚ)=2^(8*k) := by simp [w]
  have hqp : (q₂ k b:ℚ)=2^(b+2*k) := by simp [q₂]
  have h1 := ratio_le (2+2*k) b 0 0 (by omega)
  have h2 := ratio_le (b+2*k) (8*b) 0 14 (by omega)
  have h3 := ratio_le k (8*b) 0 14 (by omega)
  have h4 := ratio_le (8*k) (8*b) 0 14 (by omega)
  have h5 := ratio_le (16*k) (8*b) 0 (2*k+5) (by omega)
  have h6 := ratio_le (b+18*k) (8*b) 0 0 (by omega)
  have h7 := ratio_le (b+10*k) (8*b) 1 (2*k) (by omega)
  have eq1 : 4*(s k:ℚ)^2*rho b=2^(2+2*k)/2^b := by
    rw [hsp]; unfold rho
    rw [pow_add,show 2*k=k*2 by omega,pow_mul]
    norm_num; ring
  have eq2 : (q₂ k b:ℚ)*x b=2^(b+2*k)/2^(8*b) := by rw [hqp]; simp [x,div_eq_mul_inv]
  have eq3 : (s k:ℚ)*x b=2^k/2^(8*b) := by rw [hsp]; simp [x,div_eq_mul_inv]
  have eq4 : (w k:ℚ)*x b=2^(8*k)/2^(8*b) := by rw [hwp]; simp [x,div_eq_mul_inv]
  have eq5 : (w k:ℚ)^2*x b=2^(16*k)/2^(8*b) := by
    rw [hwp,←pow_mul,show 8*k*2=16*k by omega]; simp [x,div_eq_mul_inv]
  have eq6 : (w k:ℚ)^2*q₂ k b*x b=2^(b+18*k)/2^(8*b) := by
    rw [hwp,hqp,←pow_mul,←pow_add,show 8*k*2+(b+2*k)=b+18*k by omega]; simp [x,div_eq_mul_inv]
  have eq7 : (w k:ℚ)*q₂ k b*x b=2^(b+10*k)/2^(8*b) := by
    rw [hwp,hqp,←pow_add,show 8*k+(b+2*k)=b+10*k by omega]; simp [x,div_eq_mul_inv]
  have hrat : (1:ℚ)/2^14 ≤ 1/10000 := by norm_num
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (show 2^8 ≤ 2^k from Nat.pow_le_pow_right (by decide) hk)
  · rw [eq1]; simpa using h1
  · rw [eq2]; exact h2.trans hrat
  · rw [eq3]; exact h3.trans hrat
  · rw [eq4]; exact h4.trans hrat
  · rw [eq5]
    have he : (1:ℚ)/2^(2*k+5)=eta k/32 := by unfold eta; rw [pow_add]; norm_num; ring
    rw [pow_zero,he] at h5
    exact h5.trans (div_le_div_of_nonneg_left (by unfold eta; positivity) (by norm_num) (by norm_num))
  · rw [eq6]; simpa using h6
  · rw [eq7]
    convert h7 using 1 <;> norm_num [eta] <;> ring

theorem source_eta (k : ℕ) : (s k:ℚ)*eta k=1/2^k := by
  simp only [s,eta,Nat.cast_pow,Nat.cast_ofNat]
  rw [show 2*k=k+k by omega,pow_add]
  field_simp

theorem source_width (Δ n m k b : ℕ)
    (hn : n ≤ 2^b) (hdeg : 2*m ≤ Δ*n) (hk : 2*Δ ≤ k) :
    V38Schedule.pow2Ceil (4*s k*m) ≤ q₂ k b := by
  have hΔ : 2*Δ ≤ s k := hk.trans (V38Cutoff.coefficient_le_power k)
  have hcount : 4*s k*m ≤ q₂ k b := by
    have hdeg' : 2*m ≤ Δ*2^b := hdeg.trans (Nat.mul_le_mul_left Δ hn)
    have hmul := Nat.mul_le_mul_left (2*s k) hdeg'
    have hmul2 := Nat.mul_le_mul_right (s k*2^b) hΔ
    unfold q₂ s at *
    rw [pow_add,show 2*k=k*2 by omega,pow_mul]
    nlinarith only [hmul,hmul2]
  apply (V39PublicSchedule.pow2Ceil_le_iff _ _).2
  exact hcount

theorem collision_margin (δv ζ : ℚ) (Δ k b : ℕ)
    (hδ : 0 < δv) (hζ : 0 < ζ) (hk : commonCutoff δv ζ Δ ≤ k) (hb : 4*k ≤ b) :
    (s k:ℚ)*q₁ k/(q₂ k b:ℚ) ≤ ζ/128 := by
  have hq1 : (q₁ k:ℚ) ≤ s k := by exact_mod_cast (show q₁ k ≤ s k by unfold q₁; omega)
  have hqpos : (0:ℚ) < q₂ k b := by exact_mod_cast q₂_pos k b
  have hbound : (s k:ℚ)*q₁ k/(q₂ k b:ℚ) ≤ 1/2^b := by
    apply (div_le_iff₀ hqpos).2
    have hs : (0:ℚ) ≤ s k := by positivity
    have hh := mul_le_mul_of_nonneg_left hq1 hs
    have he : (1:ℚ)/2^b*(q₂ k b:ℚ)=(s k:ℚ)^2 := by
      simp only [q₂,s,Nat.cast_pow,Nat.cast_ofNat]
      rw [pow_add,show 2*k=k*2 by omega,pow_mul]
      field_simp
    rw [he]
    nlinarith
  exact hbound.trans ((reciprocal_le b k (by omega)).trans (cutoff_small δv ζ Δ k hδ hζ hk).2.2.2)

end CurrentAdditive.V42Schedule


