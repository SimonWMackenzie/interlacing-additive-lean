import CurrentAdditive.V39SourceProfileGuards
import CurrentAdditive.V38Schedule

/-!
Selected full-product schedule to actual source-profile guards. This is a
literal arithmetic consumer of CommonTests, not an eventual-cutoff theorem.
-/

namespace CurrentAdditive.V39FullScheduleGuards

open Paper2 Paper2.SourceProfilesInner V38Schedule

theorem word_floor (L : ℕ) (u : ℝ) (hu : 10240*(L : ℝ) ≤ u) :
    (2 : ℝ)^(-(u/1024)) ≤ ((fullX L : ℚ) : ℝ) := by
  have he : -(u/1024) ≤ -((10*L : ℕ) : ℝ) := by
    push_cast
    linarith
  calc
    _ ≤ (2 : ℝ)^(-((10*L : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    _ = ((fullX L : ℚ) : ℝ) := by
      rw [Real.rpow_neg (by norm_num),Real.rpow_natCast]
      simp [fullX,Rat.cast_inv]

theorem half_power_bound (a : ℕ) (ha : 1 ≤ a) (j : Fin 2) :
    (2 : ℝ)^a ≤ 2*(2 : ℝ)^(a-j.val) := by
  calc
    _ ≤ (2 : ℝ)^((a-j.val)+1) :=
      pow_le_pow_right₀ (by norm_num) (by have hj:=j.isLt; omega)
    _ = _ := by rw [pow_succ]; ring

theorem full_source_guards (c δv ζ : ℚ) (L m : ℕ)
    (htests : CommonTests (fullInput c L) m δv ζ) :
    (∀ j : Fin 2, RungGuards (fullQ₁ L) ((16+ell L)-j.val)
      ((fullRho L : ℚ) : ℝ) ((fullX L : ℚ) : ℝ)
      ((3/5 : ℝ)*(1/2 : ℝ)^j.val)) ∧
    (∀ j : Fin 2, RungGuards (fullQ₂ L) ((L+2*(16+ell L))-j.val)
      ((fullX L : ℚ) : ℝ) ((fullX L : ℚ) : ℝ)
      ((3/5 : ℝ)*(1/2 : ℝ)^j.val)) ∧
    (∀ j : Fin 2, RungGuards (fullS L) ((16+ell L)-j.val)
      ((fullX L : ℚ) : ℝ) ((fullX L : ℚ) : ℝ)
      (SourceProfilesReference.templateThreshold ((3/5 : ℝ)*(1/2 : ℝ)^j.val))) := by
  rcases htests with ⟨hs,_,_,h4,_,hqx,hsx,_⟩
  change 256 ≤ fullS L at hs
  change 4*(fullS L : ℚ)^2*fullRho L ≤ 1 at h4
  change (fullQ₂ L : ℚ)*fullX L ≤ 1/10000 at hqx
  change (fullS L : ℚ)*fullX L ≤ 1/10000 at hsx
  have hsR : (256 : ℝ) ≤ fullS L := by exact_mod_cast hs
  have hs0 : (0 : ℝ) ≤ fullS L := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ fullQ₂ L := Nat.cast_nonneg _
  have hρ : (0 : ℝ) < ((fullRho L : ℚ) : ℝ) := by
    norm_num only [fullRho,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]
    positivity
  have hx : (0 : ℝ) < ((fullX L : ℚ) : ℝ) := by
    norm_num only [fullX,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]
    positivity
  have h4R : 4*(fullS L : ℝ)^2*((fullRho L : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h4
  have hqxR : (fullQ₂ L : ℝ)*((fullX L : ℚ) : ℝ) ≤ 1/10000 := by
    have hh : (((fullQ₂ L : ℚ)*fullX L : ℚ) : ℝ) ≤ ((1/10000 : ℚ) : ℝ) := by
      exact_mod_cast hqx
    norm_num only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hh
    exact hh
  have hsxR : (fullS L : ℝ)*((fullX L : ℚ) : ℝ) ≤ 1/10000 := by
    have hh : (((fullS L : ℚ)*fullX L : ℚ) : ℝ) ≤ ((1/10000 : ℚ) : ℝ) := by
      exact_mod_cast hsx
    norm_num only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hh
    exact hh
  have hsr : (fullS L : ℝ)*((fullRho L : ℚ) : ℝ) ≤ 1/1000 := by
    have hscale : (1000 : ℝ) ≤ 4*(fullS L : ℝ) := by linarith
    have hm := mul_le_mul_of_nonneg_right hscale
      (by positivity : 0 ≤ (fullS L : ℝ)*((fullRho L : ℚ) : ℝ))
    nlinarith only [hm,h4R]
  have hq₁ : fullQ₁ L+2=fullS L := by unfold fullQ₁; omega
  have hqρ : (fullQ₁ L : ℝ)*((fullRho L : ℚ) : ℝ) ≤ 1/1000 :=
    (mul_le_mul_of_nonneg_right
      (by exact_mod_cast (show fullQ₁ L ≤ fullS L by omega)) hρ.le).trans hsr
  have hsa : (fullS L : ℝ)=(2 : ℝ)^(16+ell L) := by simp [fullS]
  have hqbN : fullQ₂ L=2^(L+2*(16+ell L)) := by
    unfold fullQ₂ fullS
    rw [← pow_mul,← pow_add]
    congr 1
    omega
  have hqb : (fullQ₂ L : ℝ)=(2 : ℝ)^(L+2*(16+ell L)) := by exact_mod_cast hqbN
  have hwidth : (65536 : ℝ)*((L : ℝ)+1) ≤ fullS L := by
    have hh := full_product_block_width L
    have hhN : 65536*(L+1) ≤ fullS L := by nlinarith only [hh]
    exact_mod_cast hhN
  have hqas : (fullS L : ℝ) ≤ fullQ₂ L := by exact_mod_cast fullQ₂_ge_s L
  have hworda (j : Fin 2) :
      (2 : ℝ)^(-((2 : ℝ)^((16+ell L)-j.val)/1024)) ≤ ((fullX L : ℚ) : ℝ) := by
    have hh := half_power_bound (16+ell L) (by omega) j
    rw [← hsa] at hh
    apply word_floor L
    nlinarith only [hh,hwidth,Nat.cast_nonneg (α := ℝ) L]
  have hwordb (j : Fin 2) :
      (2 : ℝ)^(-((2 : ℝ)^((L+2*(16+ell L))-j.val)/1024)) ≤ ((fullX L : ℚ) : ℝ) := by
    have hh := half_power_bound (L+2*(16+ell L)) (by omega) j
    rw [← hqb] at hh
    apply word_floor L
    nlinarith only [hh,hwidth,hqas,Nat.cast_nonneg (α := ℝ) L]
  obtain ⟨hi,ho,hr⟩ := V39SourceProfileGuards.source_population_margins
    (fullS L) (fullQ₁ L) (fullQ₂ L) (16+ell L) (L+2*(16+ell L))
    ((fullRho L : ℚ) : ℝ) ((fullX L : ℚ) : ℝ)
    (by omega) (by omega) hs hq₁ hsa hqb hqρ hqxR hsxR
  exact V39SourceProfileGuards.source_guards
    (fullS L) (fullQ₁ L) (fullQ₂ L) (16+ell L) (L+2*(16+ell L))
    ((fullRho L : ℚ) : ℝ) ((fullX L : ℚ) : ℝ)
    (by omega) (by omega) hsa hqb hρ hx
    (by linarith) (by linarith) (by linarith) hworda hwordb hi ho hr

#print axioms word_floor
#print axioms half_power_bound
#print axioms full_source_guards

end CurrentAdditive.V39FullScheduleGuards
