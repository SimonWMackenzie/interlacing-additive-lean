import CurrentAdditive.V42ExceptionMargins
import CurrentAdditive.V39GeneratedProfileGuards

/-! Numerical guards for the revised explicit source recipe.  The tuple
exception bound is applied to the whole original-label event, with its
actual rational law; this file contains no matrix-hardness premise. -/

namespace CurrentAdditive.V42GeneratedProfileGuards

open Paper2 V42Schedule

theorem scalar_parameters (k : ℕ) (hk : 200 ≤ k) :
    2 ≤ k ∧ 2 ≤ 4*k+2*k ∧
    (0 : ℝ) < (rho (4*k) : ℝ) ∧
    (0 : ℝ) < (x (4*k) : ℝ) ∧ (x (4*k) : ℝ) ≤ 1 ∧
    (s k : ℝ)*(rho (4*k) : ℝ) ≤ 1/1000 ∧
    (q₂ k (4*k) : ℝ)*(x (4*k) : ℝ) ≤ 1/10000 ∧
    (s k : ℝ)*(x (4*k) : ℝ) ≤ 1/10000 ∧
    (V38Moments.exceptionCount (x (4*k) : ℝ) 1 : ℝ) ≤ (s k : ℝ)/128 := by
  have hρ : (0 : ℝ) < (rho (4*k) : ℝ) := by unfold rho; push_cast; positivity
  have hx : (0 : ℝ) < (x (4*k) : ℝ) := by unfold x; push_cast; positivity
  have hx1 : x (4*k) ≤ 1 := by
    unfold x
    exact (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hscalar := scalar_smallness k (4*k) (by omega) le_rfl
  have hqx : (q₂ k (4*k) : ℝ)*(x (4*k) : ℝ) ≤ 1/10000 := by
    have hh : (((q₂ k (4*k) : ℚ)*x (4*k) : ℚ) : ℝ) ≤ ((1/10000 : ℚ) : ℝ) := by
      exact_mod_cast hscalar.2.2.1
    simpa only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hh
  have hsx : (s k : ℝ)*(x (4*k) : ℝ) ≤ 1/10000 := by
    have hh : (((s k : ℚ)*x (4*k) : ℚ) : ℝ) ≤ ((1/10000 : ℚ) : ℝ) := by
      exact_mod_cast hscalar.2.2.2.1
    simpa only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hh
  have hsρ : (s k : ℚ)*rho (4*k) ≤ 1/1000 := by
    have hh := ratio_le k (4*k) 0 10 (by omega)
    have he : (s k : ℚ)*rho (4*k)=2^k/2^(4*k) := by simp [s,rho,div_eq_mul_inv]
    rw [he]
    exact hh.trans (by norm_num)
  have he := generated_tuple_count k hk
  have heR : (128 : ℝ)*V38Moments.exceptionCount (x (4*k) : ℝ) 1 ≤ s k := by
    exact_mod_cast he
  refine ⟨by omega,by omega,hρ,hx,?_,?_,hqx,hsx,?_⟩
  · exact_mod_cast hx1
  · have hh : (((s k : ℚ)*rho (4*k) : ℚ) : ℝ) ≤ ((1/1000 : ℚ) : ℝ) := by
      exact_mod_cast hsρ
    simpa only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hh
  · linarith

theorem profile_guards (k : ℕ) (hk : 200 ≤ k) :
    (∀ j : Fin 2, (2 : ℝ)^(k-j.val)*(rho (4*k) : ℝ) < 1) ∧
    (∀ j : Fin 2, (2 : ℝ)^(4*k+2*k-j.val)*(x (4*k) : ℝ) < 1) ∧
    (∀ j : Fin 2, (2 : ℝ)^(k-j.val)*(x (4*k) : ℝ) < 1) ∧
    (∀ j : Fin 2,
      (((2^((k-j.val)-1)+1)+V38Moments.exceptionCount (x (4*k) : ℝ) 1 : ℕ) : ℝ)*
        (1-(2 : ℝ)^(k-j.val)*(rho (4*k) : ℝ)) ≤
        (q₁ k : ℝ)*((3/5 : ℝ)*(1/2 : ℝ)^j.val-(2 : ℝ)^(k-j.val)*(rho (4*k) : ℝ))) ∧
    (∀ j : Fin 2,
      (((2^((4*k+2*k-j.val)-1)+1)+V38Moments.exceptionCount (x (4*k) : ℝ) 1 : ℕ) : ℝ)*
        (1-(2 : ℝ)^(4*k+2*k-j.val)*(x (4*k) : ℝ)) ≤
        (q₂ k (4*k) : ℝ)*((3/5 : ℝ)*(1/2 : ℝ)^j.val-
          (2 : ℝ)^(4*k+2*k-j.val)*(x (4*k) : ℝ))) ∧
    (∀ j : Fin 2,
      (((2^((k-j.val)-1)+1)+V38Moments.exceptionCount (x (4*k) : ℝ) 1 : ℕ) : ℝ)*
        (1-(2 : ℝ)^(k-j.val)*(x (4*k) : ℝ)) ≤
        (s k : ℝ)*(SourceProfilesReference.templateThreshold ((3/5 : ℝ)*(1/2 : ℝ)^j.val)-
          (2 : ℝ)^(k-j.val)*(x (4*k) : ℝ))) := by
  obtain ⟨ha,hb,hρ,hx,_,hsρ,hqx,hsx,hE⟩ := scalar_parameters k hk
  have hs : 256 ≤ s k := (scalar_smallness k (4*k) (by omega) le_rfl).1
  have hq₁ : q₁ k+2=s k := by unfold q₁; omega
  have hqρ : (q₁ k : ℝ)*(rho (4*k) : ℝ) ≤ 1/1000 :=
    (mul_le_mul_of_nonneg_right
      (by exact_mod_cast (show q₁ k ≤ s k by omega)) hρ.le).trans hsρ
  have hsa : (s k : ℝ)=(2 : ℝ)^k := by simp [s]
  have hqb : (q₂ k (4*k) : ℝ)=(2 : ℝ)^(4*k+2*k) := by simp [q₂]
  have hqge : (s k : ℝ) ≤ q₂ k (4*k) := by
    rw [hsa,hqb]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  obtain ⟨hi,ho,hr⟩ := V39SourceProfileGuards.source_population_margins
    (s k) (q₁ k) (q₂ k (4*k)) k (4*k+2*k) (rho (4*k) : ℝ) (x (4*k) : ℝ)
    (by omega) (by omega) hs hq₁ hsa hqb hqρ hqx hsx
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro j
    have hp : (2 : ℝ)^(k-j.val) ≤ s k := by
      rw [hsa]; exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    exact (mul_le_mul_of_nonneg_right hp hρ.le).trans_lt (by linarith)
  · intro j
    have hp : (2 : ℝ)^(4*k+2*k-j.val) ≤ q₂ k (4*k) := by
      rw [hqb]; exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    exact (mul_le_mul_of_nonneg_right hp hx.le).trans_lt (by linarith)
  · intro j
    have hp : (2 : ℝ)^(k-j.val) ≤ s k := by
      rw [hsa]; exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    exact (mul_le_mul_of_nonneg_right hp hx.le).trans_lt (by linarith)
  · intro j
    have hw := V39FullScheduleGuards.half_power_bound k (by omega) j
    rw [←hsa] at hw
    exact V39GeneratedProfileGuards.budget_of_population (q₁ k) (k-j.val) (s k) _
      (rho (4*k) : ℝ) _ (by have hj:=j.isLt; omega) hs hw hE hρ.le (hi j)
  · intro j
    have hw := V39FullScheduleGuards.half_power_bound (4*k+2*k) (by omega) j
    rw [←hqb] at hw
    exact V39GeneratedProfileGuards.budget_of_population (q₂ k (4*k)) (4*k+2*k-j.val)
      (s k) _ (x (4*k) : ℝ) _ (by have hj:=j.isLt; omega) hs (hqge.trans hw) hE hx.le (ho j)
  · intro j
    have hw := V39FullScheduleGuards.half_power_bound k (by omega) j
    rw [←hsa] at hw
    exact V39GeneratedProfileGuards.budget_of_population (s k) (k-j.val) (s k) _
      (x (4*k) : ℝ) _ (by have hj:=j.isLt; omega) hs hw hE hx.le (hr j)

#print axioms scalar_parameters
#print axioms profile_guards

end CurrentAdditive.V42GeneratedProfileGuards
