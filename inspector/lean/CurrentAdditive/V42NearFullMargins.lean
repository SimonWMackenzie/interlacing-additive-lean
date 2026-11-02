import CurrentAdditive.V42CommonMargins

namespace CurrentAdditive.V42Schedule

theorem allowance_bounds (δv ζ : ℚ) :
    sourceAllowance δv ζ ≤ 1/2^16 ∧
    sourceAllowance δv ζ ≤ δv/2^16 ∧
    sourceAllowance δv ζ ≤ (ζ/256)/2^16 := by
  unfold sourceAllowance
  refine ⟨div_le_div_of_nonneg_right (min_le_left _ _) (by positivity),?_,?_⟩
  · exact div_le_div_of_nonneg_right
      ((min_le_right _ _).trans (min_le_left _ _)) (by positivity)
  · exact div_le_div_of_nonneg_right
      ((min_le_right _ _).trans (min_le_right _ _)) (by positivity)

theorem numeric_margins (δv ζ : ℚ) (Δ k b : ℕ)
    (hδ : 0 < δv) (hζ : 0 < ζ) (hk : commonCutoff δv ζ Δ ≤ k)
    (hb : 4*k ≤ b) :
    0 < eta k ∧ eta k < 1/100 ∧
    (256/255:ℚ)*(s k:ℚ)*eta k ≤ 1/1000 ∧
    eta k ≤ sourceAllowance δv ζ/(s k:ℚ) ∧
    4096*(s k:ℚ)*eta k ≤ δv/16 ∧
    8*(s k:ℚ)*q₁ k+1024*(s k:ℚ)*eta k*q₂ k b < ζ*q₂ k b/4 ∧
    2*(q₂ k b:ℚ)*x b ≤ 1/8 ∧
    2*(s k:ℚ)*x b < 999/1000 ∧
    (998/1000:ℚ) ≤ 999/1000-2*((s k-1:ℕ):ℚ)*x b := by
  obtain ⟨hk200,_,hallow,_⟩ := cutoff_small δv ζ Δ k hδ hζ hk
  obtain ⟨hs,_,hqx,hsx,_⟩ := scalar_smallness k b (by omega) hb
  have hηs : (s k:ℚ)*eta k ≤ sourceAllowance δv ζ := by
    rw [source_eta]; exact hallow
  have hηpos : 0 < eta k := by unfold eta; positivity
  have hsQ : (256:ℚ) ≤ s k := by exact_mod_cast hs
  have hspos : (0:ℚ) < s k := by exact_mod_cast s_pos k
  have hqpos : (0:ℚ) < q₂ k b := by exact_mod_cast q₂_pos k b
  obtain ⟨ha1,haδ,haζ⟩ := allowance_bounds δv ζ
  have hη1 : (s k:ℚ)*eta k ≤ 1/65536 := by norm_num at ha1; exact hηs.trans ha1
  have hηδ : (s k:ℚ)*eta k ≤ δv/65536 := by norm_num at haδ; exact hηs.trans haδ
  have hηζ : (s k:ℚ)*eta k ≤ ζ/16777216 := by
    convert hηs.trans haζ using 1 <;> norm_num <;> ring
  have hcol := collision_margin δv ζ Δ k b hδ hζ hk hb
  have hcol' : (s k:ℚ)*q₁ k ≤ ζ/128*q₂ k b :=
    (div_le_iff₀ hqpos).1 hcol
  have hmul := mul_le_mul_of_nonneg_right hηζ hqpos.le
  have hζq : (0:ℚ) < ζ*q₂ k b := mul_pos hζ hqpos
  have hsub : ((s k-1:ℕ):ℚ)=(s k:ℚ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ s k),Nat.cast_one]
  refine ⟨hηpos,by nlinarith,by nlinarith,?_,by nlinarith,?_,by linarith,by linarith,?_⟩
  · apply (le_div_iff₀ hspos).2
    nlinarith only [hηs]
  · nlinarith only [hcol',hmul,hζq]
  · rw [hsub]
    have hxpos : 0 < x b := by unfold x; positivity
    nlinarith only [hsx,hxpos]

theorem profile_scalar_margins (k b : ℕ) (hk : 8 ≤ k) (hb : 4*k ≤ b) :
    0 < rho b ∧ 0 < x b ∧ x b ≤ 1 ∧
    (s k:ℚ)*rho b ≤ 1/1000 ∧
    (q₂ k b:ℚ)*x b ≤ 1/10000 ∧
    (s k:ℚ)*x b ≤ 1/10000 := by
  obtain ⟨hs,hassign,hqx,hsx,_⟩ := scalar_smallness k b hk hb
  have hsQ : (256:ℚ) ≤ s k := by exact_mod_cast hs
  have hρ : 0 < rho b := by unfold rho; positivity
  have hx : 0 < x b := by unfold x; positivity
  have hsρ : (s k:ℚ)*rho b ≤ 1/1000 := by
    have hm := mul_le_mul_of_nonneg_right (show (1000:ℚ) ≤ 4*s k by linarith)
      (show 0 ≤ (s k:ℚ)*rho b by positivity)
    nlinarith only [hm,hassign]
  have hx1 : x b ≤ 1 := by nlinarith only [hsQ,hsx,hx]
  exact ⟨hρ,hx,hx1,hsρ,hqx,hsx⟩

#print axioms numeric_margins
#print axioms profile_scalar_margins

end CurrentAdditive.V42Schedule
