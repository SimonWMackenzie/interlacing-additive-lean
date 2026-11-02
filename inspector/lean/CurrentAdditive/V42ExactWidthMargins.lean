import CurrentAdditive.V42NumericExceptionMargins
import CurrentAdditive.V42Schedule

/-! Exact source-facing dyadic specialization of every middle-column entry
in eq:width-margins. The source's natural q1=s-2 is cast only above s>=2. -/
namespace CurrentAdditive.V42NumericMargins
open V42Schedule
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

private theorem recipe_real (k b : ℕ) :
    (q₂ k b:ℝ)=(s k:ℝ)^2/(rho b:ℝ) ∧
    (w k:ℝ)=(s k:ℝ)^8 ∧ (Q k:ℝ)=(s k:ℝ)^24 ∧
    (x b:ℝ)=(rho b:ℝ)^8 ∧ (eta k:ℝ)=1/(s k:ℝ)^2 ∧
    (theta k:ℝ)=1/(512*(s k:ℝ)^24) := by
  have h:=recipe_exact k b
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact_mod_cast h.1
  · exact_mod_cast h.2.1
  · exact_mod_cast h.2.2.1
  · exact_mod_cast h.2.2.2.1
  · have hh := congrArg (fun z:ℚ => (z:ℝ)) h.2.2.2.2.1
    push_cast at hh
    exact hh
  · have hθ : theta k=1/(512*(s k:ℚ)^24) := by
      rw [h.2.2.2.2.2.1,h.2.2.1]
      simp
    have hh := congrArg (fun z:ℚ => (z:ℝ)) hθ
    push_cast at hh
    exact hh

private theorem real_domain (k b : ℕ) (hb : 4*k ≤ b) :
    1 ≤ (s k:ℝ) ∧ 0<(rho b:ℝ) ∧ (rho b:ℝ) ≤ (s k:ℝ)^(-(4:ℝ)) := by
  have hs : 1 ≤ (s k:ℝ) := by exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2^k)
  have hsp : 0<(s k:ℝ) := lt_of_lt_of_le (by norm_num) hs
  have hp : 0<(rho b:ℝ) := by unfold rho; positivity
  refine ⟨hs,hp,?_⟩
  have hrat := reciprocal_le b (4*k) hb
  have he : (1:ℚ)/2^(4*k)=1/(s k:ℚ)^4 := by
    simp only [s,Nat.cast_pow,Nat.cast_ofNat]
    rw [←pow_mul]
    congr 2
    omega
  rw [he] at hrat
  have hrat' : rho b ≤ 1/(s k:ℚ)^4 := by simpa only [rho] using hrat
  have hh := (Rat.cast_le (K:=ℝ)).mpr hrat'
  push_cast at hh
  rw [Real.rpow_neg hsp.le,Real.rpow_ofNat]
  simpa only [one_div] using hh

/-- All eleven literal quantity-to-middle-column bounds for the actual
V42Schedule parameters. Fractional exponents are real, so no natural division occurs. -/
theorem width_margins_middle (k b n m Δ : ℕ) (hk : 1 ≤ k) (hb : 4*k ≤ b)
    (hn : n ≤ 2^b) (hdeg : 2*m ≤ Δ*n) :
    (s k:ℝ)*(eta k:ℝ) ≤ (s k:ℝ)^(-(1:ℝ)) ∧
    4*(s k:ℝ)*m/(q₂ k b:ℝ) ≤ 2*(Δ:ℝ)/(s k:ℝ) ∧
    (s k:ℝ)^2*(rho b:ℝ) ≤ (s k:ℝ)^(-(2:ℝ)) ∧
    (s k:ℝ)*(q₁ k:ℝ)/(q₂ k b:ℝ) ≤ (s k:ℝ)^(-(4:ℝ)) ∧
    max ((q₂ k b:ℝ)*(x b:ℝ)) (max ((s k:ℝ)*(x b:ℝ)) ((w k:ℝ)*(x b:ℝ))) ≤
      (s k:ℝ)^(-(24:ℝ)) ∧
    (w k:ℝ)^2*(x b:ℝ)/(eta k:ℝ) ≤ (s k:ℝ)^(-(14:ℝ)) ∧
    (w k:ℝ)^2*(q₂ k b:ℝ)*(x b:ℝ) ≤ (s k:ℝ)^(-(10:ℝ)) ∧
    (w k:ℝ)*(q₂ k b:ℝ)*(x b:ℝ)/(eta k:ℝ) ≤ (s k:ℝ)^(-(16:ℝ)) ∧
    (V38Moments.exceptionCount ((theta k:ℝ)/4) 1:ℝ)/((s k:ℝ)*(q₂ k b:ℝ)) ≤
      (2:ℝ)^85*(s k:ℝ)^(-(53:ℝ)/8) ∧
    (V38Schedule.C128:ℝ)*(s k:ℝ)^(-(128:ℝ))/(theta k:ℝ)=
      512*(V38Schedule.C128:ℝ)*(s k:ℝ)^(-(104:ℝ)) ∧
    2*(s k:ℝ)*(2*(V38Moments.exceptionCount (theta k:ℝ) ((eta k:ℝ)/2):ℝ))/
        ((eta k:ℝ)*(w k:ℝ)) ≤ (2:ℝ)^89*(s k:ℝ)^(-(5:ℝ)/8) := by
  obtain ⟨hs,hρ,hsmall⟩ := real_domain k b hb
  have hsp : 0<(s k:ℝ) := lt_of_lt_of_le (by norm_num) hs
  have hs2 : 2 ≤ s k := by
    change 2^1 ≤ 2^k
    exact Nat.pow_le_pow_right (by decide) hk
  have hq1 : (q₁ k:ℝ)=(s k:ℝ)-2 := by
    unfold q₁
    rw [Nat.cast_sub hs2]
    norm_num
  have hnR : (n:ℝ) ≤ 1/(rho b:ℝ) := by
    have hh : (n:ℝ) ≤ (2:ℝ)^b := by exact_mod_cast hn
    simpa [rho] using hh
  have hdegR : (2:ℝ)*m ≤ (Δ:ℝ)*n := by exact_mod_cast hdeg
  obtain ⟨hq,hw,hQ,hx,hη,hθ⟩ := recipe_real k b
  rw [hq1,hq,hw,hx,hη,hθ]
  exact ⟨(source_eta _ hsp).le,edge_width _ _ _ _ _ hsp hρ (by positivity) hnR hdegR,
    small_mass _ _ hs hρ.le hsmall,collision _ _ hsp hρ hsmall,
    max_width_x _ _ hs hρ hsmall,w2x_over_eta _ _ hs hρ.le hsmall,
    w2q2x _ _ hs hρ hsmall,wq2x_over_eta _ _ hs hρ hsmall,
    quarter_exception_ratio _ _ hs hρ hsmall,flag_ratio_identity _ _ hsp,
    owner_exception_ratio _ hs⟩

/-- The two exact exceptional-coordinate substitutions stated after the table. -/
theorem exception_substitutions (k : ℕ) :
    (V38Moments.exceptionCount ((theta k:ℝ)/4) 1:ℝ) ≤
      (2:ℝ)^85*(s k:ℝ)^((3:ℝ)/8) ∧
    2*(V38Moments.exceptionCount (theta k:ℝ) ((eta k:ℝ)/2):ℝ) ≤
      (2:ℝ)^88*(s k:ℝ)^((35:ℝ)/8) := by
  have hs : 1 ≤ (s k:ℝ) := by exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2^k)
  obtain ⟨_,_,_,_,hη,hθ⟩ := recipe_real k 0
  rw [hη,hθ]
  exact ⟨quarter_exception_bound _ hs,owner_exception_bound _ hs⟩

#print axioms width_margins_middle
#print axioms exception_substitutions
end CurrentAdditive.V42NumericMargins




