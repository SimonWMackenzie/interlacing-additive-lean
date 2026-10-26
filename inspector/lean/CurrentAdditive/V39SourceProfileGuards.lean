import CurrentAdditive.V39ActualSourceProfiles

/-! Arithmetic bridge from the selected source's scalar margins to the
retained-block guards. No matrix or protocol lower bound is assumed here. -/

namespace CurrentAdditive.V39SourceProfileGuards

open Paper2 Paper2.SourceProfilesInner

theorem rung_of_margin (q a : ℕ) (θ x β : ℝ)
    (ha : 4 ≤ a) (hθ : 0 < θ) (ht : (2 : ℝ)^a*θ < 1)
    (hword : (2 : ℝ)^(-((2 : ℝ)^a/1024)) ≤ x)
    (hmargin : (9/16 : ℝ)*(2 : ℝ)^a ≤ (q : ℝ)*(β-(2 : ℝ)^a*θ)) :
    RungGuards q a θ x β := by
  have hcopies : (StrongSeed.copies a : ℝ)=(9/16 : ℝ)*(2 : ℝ)^a := by
    have hsplit : (2 : ℝ)^a=16*(2 : ℝ)^(a-4) := by
      exact_mod_cast StrongSeed.pow_split a ha
    rw [hsplit]
    simp [StrongSeed.copies]
    ring
  refine ⟨ha,hθ,ht,hword,?_⟩
  rw [hcopies]
  have ht0 : 0 ≤ (2 : ℝ)^a*θ := by positivity
  have hc0 : 0 ≤ (9/16 : ℝ)*(2 : ℝ)^a := by positivity
  exact (mul_le_of_le_one_right hc0 (by linarith : 1-(2 : ℝ)^a*θ ≤ 1)).trans hmargin

/-- Every source population calculation is reduced to the three scalar
inequalities displayed in the manuscript. The only word-density inputs
are the two full-product floors, shared by the first/reference interlaces.
The full schedule supplies these arithmetic statements separately. -/
theorem source_guards
    (s q₁ q₂ a b : ℕ) (ρ x : ℝ)
    (ha : 5 ≤ a) (hb : 5 ≤ b)
    (hsa : (s : ℝ)=(2 : ℝ)^a) (hqb : (q₂ : ℝ)=(2 : ℝ)^b)
    (hρ : 0 < ρ) (hx : 0 < x)
    (hsρ : (s : ℝ)*ρ < 1) (hqx : (q₂ : ℝ)*x < 1) (hsx : (s : ℝ)*x < 1)
    (hworda : ∀ j : Fin 2, (2 : ℝ)^(-((2 : ℝ)^(a-j.val)/1024)) ≤ x)
    (hwordb : ∀ j : Fin 2, (2 : ℝ)^(-((2 : ℝ)^(b-j.val)/1024)) ≤ x)
    (hinner : ∀ j : Fin 2, (9/16 : ℝ)*(2 : ℝ)^(a-j.val) ≤
      (q₁ : ℝ)*((3/5 : ℝ)*(1/2 : ℝ)^j.val-(2 : ℝ)^(a-j.val)*ρ))
    (houter : ∀ j : Fin 2, (9/16 : ℝ)*(2 : ℝ)^(b-j.val) ≤
      (q₂ : ℝ)*((3/5 : ℝ)*(1/2 : ℝ)^j.val-(2 : ℝ)^(b-j.val)*x))
    (hreference : ∀ j : Fin 2, (9/16 : ℝ)*(2 : ℝ)^(a-j.val) ≤
      (s : ℝ)*(SourceProfilesReference.templateThreshold
        ((3/5 : ℝ)*(1/2 : ℝ)^j.val)-(2 : ℝ)^(a-j.val)*x)) :
    (∀ j : Fin 2, RungGuards q₁ (a-j.val) ρ x ((3/5 : ℝ)*(1/2 : ℝ)^j.val)) ∧
    (∀ j : Fin 2, RungGuards q₂ (b-j.val) x x ((3/5 : ℝ)*(1/2 : ℝ)^j.val)) ∧
    (∀ j : Fin 2, RungGuards s (a-j.val) x x
      (SourceProfilesReference.templateThreshold ((3/5 : ℝ)*(1/2 : ℝ)^j.val))) := by
  have hpa (j : Fin 2) : (2 : ℝ)^(a-j.val) ≤ s := by
    rw [hsa]
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hpb (j : Fin 2) : (2 : ℝ)^(b-j.val) ≤ q₂ := by
    rw [hqb]
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  refine ⟨?_,?_,?_⟩
  · intro j
    exact rung_of_margin q₁ (a-j.val) ρ x _ (by have hj:=j.isLt; omega) hρ
      ((mul_le_mul_of_nonneg_right (hpa j) hρ.le).trans_lt hsρ)
      (hworda j) (hinner j)
  · intro j
    exact rung_of_margin q₂ (b-j.val) x x _ (by have hj:=j.isLt; omega) hx
      ((mul_le_mul_of_nonneg_right (hpb j) hx.le).trans_lt hqx)
      (hwordb j) (houter j)
  · intro j
    exact rung_of_margin s (a-j.val) x x _ (by have hj:=j.isLt; omega) hx
      ((mul_le_mul_of_nonneg_right (hpa j) hx.le).trans_lt hsx)
      (hworda j) (hreference j)

/-- The three displayed retained-block counts from `src:profiles` are
enough for the exact-p selection. The bounds here follow directly from
the scalar source tests; they contain no communication assumption. -/
theorem source_population_margins
    (s q₁ q₂ a b : ℕ) (ρ x : ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hs : 256 ≤ s) (hq : q₁+2=s)
    (hsa : (s : ℝ)=(2 : ℝ)^a) (hqb : (q₂ : ℝ)=(2 : ℝ)^b)
    (hqρ : (q₁ : ℝ)*ρ ≤ 1/1000)
    (hqx : (q₂ : ℝ)*x ≤ 1/10000) (hsx : (s : ℝ)*x ≤ 1/10000) :
    (∀ j : Fin 2, (9/16 : ℝ)*(2 : ℝ)^(a-j.val) ≤
      (q₁ : ℝ)*((3/5 : ℝ)*(1/2 : ℝ)^j.val-(2 : ℝ)^(a-j.val)*ρ)) ∧
    (∀ j : Fin 2, (9/16 : ℝ)*(2 : ℝ)^(b-j.val) ≤
      (q₂ : ℝ)*((3/5 : ℝ)*(1/2 : ℝ)^j.val-(2 : ℝ)^(b-j.val)*x)) ∧
    (∀ j : Fin 2, (9/16 : ℝ)*(2 : ℝ)^(a-j.val) ≤
      (s : ℝ)*(SourceProfilesReference.templateThreshold
        ((3/5 : ℝ)*(1/2 : ℝ)^j.val)-(2 : ℝ)^(a-j.val)*x)) := by
  have hsa' : (2 : ℝ)^a=(s : ℝ) := hsa.symm
  have hqb' : (2 : ℝ)^b=(q₂ : ℝ) := hqb.symm
  have hpreda : (2 : ℝ)^(a-1)=(s : ℝ)/2 := by
    have hsuc : a=(a-1)+1 := by omega
    rw [hsuc,pow_succ] at hsa
    linarith
  have hpredb : (2 : ℝ)^(b-1)=(q₂ : ℝ)/2 := by
    have hsuc : b=(b-1)+1 := by omega
    rw [hsuc,pow_succ] at hqb
    linarith
  have hsR : (256 : ℝ) ≤ s := by exact_mod_cast hs
  have hqR : (q₁ : ℝ)+2=s := by exact_mod_cast hq
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ q₂ := Nat.cast_nonneg _
  have hinner : (9/16 : ℝ)*(s : ℝ) ≤ (q₁ : ℝ)*(3/5-(s : ℝ)*ρ) := by
    have hm := mul_le_mul_of_nonneg_left hqρ hs0
    nlinarith only [hm,hsR,hqR]
  have houter : (9/16 : ℝ)*(q₂ : ℝ) ≤ (q₂ : ℝ)*(3/5-(q₂ : ℝ)*x) := by
    have hm := mul_le_mul_of_nonneg_left hqx hq0
    nlinarith only [hm,hq0]
  have href0 : (9/16 : ℝ)*(s : ℝ) ≤ (s : ℝ)*(763/1275-(s : ℝ)*x) := by
    have hm := mul_le_mul_of_nonneg_left hsx hs0
    nlinarith only [hm,hs0]
  have href1 : (9/16 : ℝ)*((s : ℝ)/2) ≤ (s : ℝ)*(379/1275-((s : ℝ)/2)*x) := by
    have hm := mul_le_mul_of_nonneg_left hsx hs0
    nlinarith only [hm,hs0]
  refine ⟨?_,?_,?_⟩
  · intro j
    fin_cases j
    · simpa only [Fin.val_zero,Nat.sub_zero,pow_zero,mul_one,hsa'] using hinner
    · norm_num only [Fin.val_one,pow_one,hpreda]
      nlinarith only [hinner]
  · intro j
    fin_cases j
    · simpa only [Fin.val_zero,Nat.sub_zero,pow_zero,mul_one,hqb'] using houter
    · norm_num only [Fin.val_one,pow_one,hpredb]
      nlinarith only [houter]
  · intro j
    fin_cases j
    · norm_num only [Fin.val_zero,Nat.sub_zero,pow_zero,mul_one,hsa',
        SourceProfilesReference.templateThreshold]
      norm_num at href0 ⊢
      exact href0
    · norm_num only [Fin.val_one,pow_one,hpreda,SourceProfilesReference.templateThreshold]
      norm_num at href1 ⊢
      exact href1

#print axioms rung_of_margin
#print axioms source_guards
#print axioms source_population_margins

end CurrentAdditive.V39SourceProfileGuards
