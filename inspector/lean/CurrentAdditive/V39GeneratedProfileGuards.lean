import CurrentAdditive.V39ExceptionBudget
import CurrentAdditive.V39SourceProfileGuards
import CurrentAdditive.V39FullScheduleGuards
import CurrentAdditive.GeneratedCutoffApplications

/-!
Current generated source-profile scalar guards.  The whole retained event
has lower bound v=x_g and tolerance τ=1. Its actual exception count is
bounded by the checker's literal ebar; no conditioning or lower-bound
conclusion is assumed by this arithmetic module.
-/

namespace CurrentAdditive.V39GeneratedProfileGuards

open Paper2 Paper2.SourceProfilesInner V38Schedule

theorem budget_of_population (q k s e : ℕ) (θ β : ℝ)
    (hk : 1 ≤ k) (hs : 256 ≤ s)
    (hwidth : (s : ℝ) ≤ 2*(2 : ℝ)^k)
    (he : (e : ℝ) ≤ (s : ℝ)/128) (hθ : 0 ≤ θ)
    (hpop : (9/16 : ℝ)*(2 : ℝ)^k ≤ (q : ℝ)*(β-(2 : ℝ)^k*θ)) :
    (((2^(k-1)+1+e : ℕ) : ℝ))*(1-(2 : ℝ)^k*θ) ≤
      (q : ℝ)*(β-(2 : ℝ)^k*θ) := by
  have hhalf : (2 : ℝ)^(k-1)=(2 : ℝ)^k/2 := by
    have hsuc : k=(k-1)+1 := by omega
    rw [hsuc,pow_succ]
    rw [show (k-1+1)-1=k-1 by omega]
    ring
  have hsR : (256 : ℝ) ≤ s := by exact_mod_cast hs
  have hcount : ((2^(k-1)+1+e : ℕ) : ℝ) ≤ (9/16 : ℝ)*(2 : ℝ)^k := by
    push_cast
    rw [hhalf]
    linarith
  have hcount0 : (0 : ℝ) ≤ ((2^(k-1)+1+e : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht0 : 0 ≤ (2 : ℝ)^k*θ := by positivity
  exact (mul_le_of_le_one_right hcount0
    (by linarith : 1-(2 : ℝ)^k*θ ≤ 1)).trans (hcount.trans hpop)

theorem scalar_parameters (c δv ζ : ℚ) (L m : ℕ)
    (htests : GeneratedTests c L m δv ζ) :
    2 ≤ quarterCeil L ∧ 2 ≤ 4*L ∧
    (0 : ℝ) < ((generatedRho L : ℚ) : ℝ) ∧
    (0 : ℝ) < ((generatedX L : ℚ) : ℝ) ∧
    ((generatedX L : ℚ) : ℝ) ≤ 1 ∧
    (generatedS L : ℝ)*((generatedRho L : ℚ) : ℝ) ≤ 1/1000 ∧
    (generatedQ₂ L : ℝ)*((generatedX L : ℚ) : ℝ) ≤ 1/10000 ∧
    (generatedS L : ℝ)*((generatedX L : ℚ) : ℝ) ≤ 1/10000 ∧
    (V38Moments.exceptionCount ((generatedX L : ℚ) : ℝ) 1 : ℝ) ≤ (generatedS L : ℝ)/128 := by
  have heb := htests.2.1
  rcases htests.1 with ⟨hs,_,_,h4,_,hqx,hsx,_⟩
  change 256 ≤ generatedS L at hs
  change 4*(generatedS L : ℚ)^2*generatedRho L ≤ 1 at h4
  change (generatedQ₂ L : ℚ)*generatedX L ≤ 1/10000 at hqx
  change (generatedS L : ℚ)*generatedX L ≤ 1/10000 at hsx
  have ha8 : 8 ≤ quarterCeil L := by
    apply (Nat.pow_le_pow_iff_right (by decide : (1 : ℕ)<2)).1
    simpa only [generatedS,show (2 : ℕ)^8=256 by norm_num] using hs
  have hL : 1 ≤ L := by unfold quarterCeil at ha8; omega
  have hρ : (0 : ℝ) < ((generatedRho L : ℚ) : ℝ) := by
    simp only [generatedRho,generatedN,Rat.cast_div,Rat.cast_one,Rat.cast_natCast,
      Nat.cast_pow,Nat.cast_ofNat]
    positivity
  have hx : (0 : ℝ) < ((generatedX L : ℚ) : ℝ) := by
    rw [V39ExceptionBudget.generated_x_eq_dyadic]
    exact V39ExceptionBudget.dyadic_pos _
  have hx1 : ((generatedX L : ℚ) : ℝ) ≤ 1 := by
    rw [V39ExceptionBudget.generated_x_eq_dyadic]
    exact V39ExceptionBudget.dyadic_le_one _
  have hsR : (256 : ℝ) ≤ generatedS L := by exact_mod_cast hs
  have h4R : 4*(generatedS L : ℝ)^2*((generatedRho L : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h4
  have hqxR : (generatedQ₂ L : ℝ)*((generatedX L : ℚ) : ℝ) ≤ 1/10000 := by
    have hh : (((generatedQ₂ L : ℚ)*generatedX L : ℚ) : ℝ) ≤ ((1/10000 : ℚ) : ℝ) := by exact_mod_cast hqx
    norm_num only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hh
    exact hh
  have hsxR : (generatedS L : ℝ)*((generatedX L : ℚ) : ℝ) ≤ 1/10000 := by
    have hh : (((generatedS L : ℚ)*generatedX L : ℚ) : ℝ) ≤ ((1/10000 : ℚ) : ℝ) := by exact_mod_cast hsx
    norm_num only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hh
    exact hh
  have hsr : (generatedS L : ℝ)*((generatedRho L : ℚ) : ℝ) ≤ 1/1000 := by
    have hscale : (1000 : ℝ) ≤ 4*(generatedS L : ℝ) := by linarith
    have hm := mul_le_mul_of_nonneg_right hscale
      (by positivity : 0 ≤ (generatedS L : ℝ)*((generatedRho L : ℚ) : ℝ))
    nlinarith only [hm,h4R]
  have heN : V38Moments.exceptionCount ((generatedX L : ℚ) : ℝ) 1 ≤ generatedS L/128 :=
    (V39ExceptionBudget.generated_exception_le_ebar L).trans heb
  have heMul : 128*V38Moments.exceptionCount ((generatedX L : ℚ) : ℝ) 1 ≤ generatedS L := by omega
  have heR : (V38Moments.exceptionCount ((generatedX L : ℚ) : ℝ) 1 : ℝ) ≤ (generatedS L : ℝ)/128 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ)<128)).2
    exact_mod_cast (show V38Moments.exceptionCount ((generatedX L : ℚ) : ℝ) 1*128 ≤ generatedS L by omega)
  exact ⟨by omega,by omega,hρ,hx,hx1,hsr,hqxR,hsxR,heR⟩

theorem scale_guards (c δv ζ : ℚ) (L m : ℕ)
    (htests : GeneratedTests c L m δv ζ) :
    (∀ j : Fin 2, (2 : ℝ)^(quarterCeil L-j.val)*((generatedRho L : ℚ) : ℝ) < 1) ∧
    (∀ j : Fin 2, (2 : ℝ)^(4*L-j.val)*((generatedX L : ℚ) : ℝ) < 1) ∧
    (∀ j : Fin 2, (2 : ℝ)^(quarterCeil L-j.val)*((generatedX L : ℚ) : ℝ) < 1) := by
  obtain ⟨_,_,hρ,hx,_,hsρ,hqx,hsx,_⟩ := scalar_parameters c δv ζ L m htests
  have hsa : (generatedS L : ℝ)=(2 : ℝ)^quarterCeil L := by simp [generatedS]
  have hqbN : generatedQ₂ L=2^(4*L) := by
    unfold generatedQ₂ generatedN
    rw [← pow_mul]
    congr 1
    omega
  have hqb : (generatedQ₂ L : ℝ)=(2 : ℝ)^(4*L) := by exact_mod_cast hqbN
  refine ⟨?_,?_,?_⟩
  · intro j
    have hp : (2 : ℝ)^(quarterCeil L-j.val) ≤ generatedS L := by
      rw [hsa]
      exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    exact (mul_le_mul_of_nonneg_right hp hρ.le).trans_lt (by linarith)
  · intro j
    have hp : (2 : ℝ)^(4*L-j.val) ≤ generatedQ₂ L := by
      rw [hqb]
      exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    exact (mul_le_mul_of_nonneg_right hp hx.le).trans_lt (by linarith)
  · intro j
    have hp : (2 : ℝ)^(quarterCeil L-j.val) ≤ generatedS L := by
      rw [hsa]
      exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    exact (mul_le_mul_of_nonneg_right hp hx.le).trans_lt (by linarith)

theorem population_budgets (c δv ζ : ℚ) (L m : ℕ)
    (htests : GeneratedTests c L m δv ζ) :
    (∀ j : Fin 2,
      (((2^((quarterCeil L-j.val)-1)+1)+V38Moments.exceptionCount ((generatedX L : ℚ) : ℝ) 1 : ℕ) : ℝ)*
        (1-(2 : ℝ)^(quarterCeil L-j.val)*((generatedRho L : ℚ) : ℝ)) ≤
        (generatedQ₁ L : ℝ)*((3/5 : ℝ)*(1/2 : ℝ)^j.val-(2 : ℝ)^(quarterCeil L-j.val)*((generatedRho L : ℚ) : ℝ))) ∧
    (∀ j : Fin 2,
      (((2^((4*L-j.val)-1)+1)+V38Moments.exceptionCount ((generatedX L : ℚ) : ℝ) 1 : ℕ) : ℝ)*
        (1-(2 : ℝ)^(4*L-j.val)*((generatedX L : ℚ) : ℝ)) ≤
        (generatedQ₂ L : ℝ)*((3/5 : ℝ)*(1/2 : ℝ)^j.val-(2 : ℝ)^(4*L-j.val)*((generatedX L : ℚ) : ℝ))) ∧
    (∀ j : Fin 2,
      (((2^((quarterCeil L-j.val)-1)+1)+V38Moments.exceptionCount ((generatedX L : ℚ) : ℝ) 1 : ℕ) : ℝ)*
        (1-(2 : ℝ)^(quarterCeil L-j.val)*((generatedX L : ℚ) : ℝ)) ≤
        (generatedS L : ℝ)*(SourceProfilesReference.templateThreshold ((3/5 : ℝ)*(1/2 : ℝ)^j.val)-
          (2 : ℝ)^(quarterCeil L-j.val)*((generatedX L : ℚ) : ℝ))) := by
  obtain ⟨ha,hb,hρ,hx,_,hsρ,hqx,hsx,hE⟩ := scalar_parameters c δv ζ L m htests
  have hs : 256 ≤ generatedS L := htests.1.1
  have hq₁ : generatedQ₁ L+2=generatedS L := by unfold generatedQ₁; omega
  have hqρ : (generatedQ₁ L : ℝ)*((generatedRho L : ℚ) : ℝ) ≤ 1/1000 :=
    (mul_le_mul_of_nonneg_right
      (by exact_mod_cast (show generatedQ₁ L ≤ generatedS L by omega)) hρ.le).trans hsρ
  have hsa : (generatedS L : ℝ)=(2 : ℝ)^quarterCeil L := by simp [generatedS]
  have hqbN : generatedQ₂ L=2^(4*L) := by
    unfold generatedQ₂ generatedN
    rw [← pow_mul]
    congr 1
    omega
  have hqb : (generatedQ₂ L : ℝ)=(2 : ℝ)^(4*L) := by exact_mod_cast hqbN
  have hqgeN : generatedS L ≤ generatedQ₂ L := by
    rw [hqbN]
    unfold generatedS
    apply Nat.pow_le_pow_right (by decide : 0<2)
    unfold quarterCeil
    have hL : 1 ≤ L := by omega
    omega
  have hqge : (generatedS L : ℝ) ≤ generatedQ₂ L := by exact_mod_cast hqgeN
  obtain ⟨hi,ho,hr⟩ := V39SourceProfileGuards.source_population_margins
    (generatedS L) (generatedQ₁ L) (generatedQ₂ L) (quarterCeil L) (4*L)
    ((generatedRho L : ℚ) : ℝ) ((generatedX L : ℚ) : ℝ)
    (by omega) (by omega) hs hq₁ hsa hqb hqρ hqx hsx
  refine ⟨?_,?_,?_⟩
  · intro j
    have hwidth := V39FullScheduleGuards.half_power_bound (quarterCeil L) (by omega) j
    rw [← hsa] at hwidth
    exact budget_of_population (generatedQ₁ L) (quarterCeil L-j.val)
      (generatedS L) _ ((generatedRho L : ℚ) : ℝ) _
      (by have hj:=j.isLt; omega) hs hwidth hE hρ.le (hi j)
  · intro j
    have hwidth := V39FullScheduleGuards.half_power_bound (4*L) (by omega) j
    rw [← hqb] at hwidth
    exact budget_of_population (generatedQ₂ L) (4*L-j.val)
      (generatedS L) _ ((generatedX L : ℚ) : ℝ) _
      (by have hj:=j.isLt; omega) hs (hqge.trans hwidth) hE hx.le (ho j)
  · intro j
    have hwidth := V39FullScheduleGuards.half_power_bound (quarterCeil L) (by omega) j
    rw [← hsa] at hwidth
    exact budget_of_population (generatedS L) (quarterCeil L-j.val)
      (generatedS L) _ ((generatedX L : ℚ) : ℝ) _
      (by have hj:=j.isLt; omega) hs hwidth hE hx.le (hr j)

#print axioms budget_of_population
#print axioms scalar_parameters
#print axioms scale_guards
#print axioms population_budgets

end CurrentAdditive.V39GeneratedProfileGuards
