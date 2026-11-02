import CurrentAdditive.EvenMomentGeneral
import CurrentAdditive.ConditioningMoments

/-!
Separate proof of the broader real-valued even-moment statement from selected
v38. This file is deliberately separate from the frozen indicator consumer
packet.
-/

namespace V38GeneralMoment

open Paper2 Paper2.FiniteLaw CurrentAdditive.EvenMoment
open scoped BigOperators

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

variable {Ω : Type*} [Fintype Ω]

/-- One bounded centered real variable has the sub-Gaussian MGF bound under
an actual normalized finite law. This uses Hoeffding's chord inequality and
the finite law's centering equation. -/
theorem bounded_centered_mgf (ν : FiniteLaw Ω) (X : Ω → ℝ)
    (hcenter : ex ν X = 0) (hbound : ∀ ω, |X ω| ≤ 1) (t : ℝ) :
    ex ν (fun ω => Real.exp (t * X ω)) ≤ Real.exp (t^2/2) := by
  classical
  have hpoint (ω : Ω) :
      Real.exp (t * X ω) ≤ Real.cosh t + X ω * Real.sinh t := by
    simpa only [mul_comm t (X ω)] using
      Real.exp_mul_le_cosh_add_mul_sinh (hbound ω) t
  have hsum : ex ν (fun ω => Real.exp (t * X ω)) ≤
      ex ν (fun ω => Real.cosh t + X ω * Real.sinh t) := by
    unfold ex
    exact Finset.sum_le_sum (fun ω _ =>
      mul_le_mul_of_nonneg_left (hpoint ω) (ν.nonneg ω))
  have hmean : ex ν (fun ω => Real.cosh t + X ω * Real.sinh t) =
      Real.cosh t := by
    unfold ex at hcenter ⊢
    calc
      (∑ ω, ν.weight ω * (Real.cosh t + X ω * Real.sinh t)) =
          Real.cosh t * (∑ ω, ν.weight ω) +
            Real.sinh t * (∑ ω, ν.weight ω * X ω) := by
              calc
                _ = ∑ ω, (Real.cosh t * ν.weight ω +
                    Real.sinh t * (ν.weight ω * X ω)) := by
                      apply Finset.sum_congr rfl
                      intro ω _
                      ring
                _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = Real.cosh t := by rw [ν.total, hcenter]; ring
  exact hsum.trans (hmean.le.trans (Real.cosh_le_exp_half_sq t))

/-- Full independent-proxy MGF for individually bounded, centered real
variables; the variables need not have identical one-point laws. -/
theorem iid_bounded_centered_mgf (ν : FiniteLaw Ω)
    (m : ℕ) (X : Fin m → Ω → ℝ)
    (hcenter : ∀ i, ex ν (X i) = 0)
    (hbound : ∀ i ω, |X i ω| ≤ 1) (t : ℝ) :
    ex (ν.iid m) (fun ws => Real.exp (t * ∑ i : Fin m, X i (ws i))) ≤
      Real.exp ((m : ℝ) * t^2/2) := by
  classical
  rw [iid_exp_sum_indexed]
  have hprod :
      (∏ i : Fin m, ex ν (fun ω => Real.exp (t * X i ω))) ≤
        ∏ _i : Fin m, Real.exp (t^2/2) := by
    apply Finset.prod_le_prod
    · intro i _
      unfold ex
      exact Finset.sum_nonneg (fun ω _ =>
        mul_nonneg (ν.nonneg ω) (Real.exp_pos _).le)
    · intro i _
      exact bounded_centered_mgf ν (X i) (hcenter i) (hbound i) t
  calc
    _ ≤ ∏ _i : Fin m, Real.exp (t^2/2) := hprod
    _ = Real.exp ((m : ℝ)*t^2/2) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Real.exp_nat_mul]
      congr 1
      ring

private theorem factorial_even_le_pair_pow (r : ℕ) (hr : 0 < r) :
    Nat.factorial (2 * r) ≤ (r * (r + 1)) ^ r := by
  have hfac : Nat.factorial (2 * r) =
      ∏ i ∈ Finset.range r, (i + 1) * (2 * r - i) := by
    rw [Nat.factorial_eq_prod_range_add_one,
      show 2 * r = r + r by omega, Finset.prod_range_add]
    have hreflect : (∏ i ∈ Finset.range r, (r + i + 1)) =
        ∏ i ∈ Finset.range r, (2 * r - i) := by
      rw [← Finset.prod_range_reflect (fun i => r + i + 1) r]
      apply Finset.prod_congr rfl
      intro i hi
      have hii := Finset.mem_range.mp hi
      omega
    rw [hreflect, ← Finset.prod_mul_distrib]
    simp only [two_mul]
  rw [hfac]
  calc
    _ ≤ ∏ _i ∈ Finset.range r, (r * (r + 1)) := by
      apply Finset.prod_le_prod
      · intro i hi
        omega
      · intro i hi
        have hii := Finset.mem_range.mp hi
        have h1 : (r - 1 - i) + i = r - 1 := by omega
        have h2 : (r - i) + i = r := by omega
        have h3 : (2 * r - i) + i = 2 * r := by omega
        have hp : 0 ≤ (r - 1 - i) * (r - i) := Nat.zero_le _
        nlinarith
    _ = _ := by simp [Finset.prod_const]

/-- The independent comparison law satisfies the literal v38 constant for
every half-order `r ≥ 3`; small orders require a direct second/fourth-moment
argument. -/
theorem iid_bounded_centered_even_moment_ge_three
    (ν : FiniteLaw Ω) (m r : ℕ) (hr : 3 ≤ r)
    (X : Fin m → Ω → ℝ)
    (hcenter : ∀ i, ex ν (X i) = 0)
    (hbound : ∀ i ω, |X i ω| ≤ 1) :
    ex (ν.iid m) (fun ws => |∑ i : Fin m, X i (ws i)|^(2*r)) ≤
      (((r : ℝ)^2) * m)^r := by
  classical
  let S : (Fin m → Ω) → ℝ := fun ws => ∑ i : Fin m, X i (ws i)
  change ex (ν.iid m) (fun ws => |S ws|^(2*r)) ≤ _
  by_cases hm : m = 0
  · subst m
    have hr0 : r ≠ 0 := by omega
    simp [S, ex, Paper2.FiniteLaw.iid, hr0]
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have hrpos : (0 : ℝ) < r := Nat.cast_pos.mpr (by omega)
  let t : ℝ := Real.sqrt (2*(r : ℝ)/(m : ℝ))
  have htarg : 0 < 2*(r : ℝ)/(m : ℝ) := by positivity
  have ht : 0 < t := Real.sqrt_pos.2 htarg
  have ht2 : t^2 = 2*(r : ℝ)/(m : ℝ) := Real.sq_sqrt htarg.le
  have hmt : (m : ℝ)*t^2/2 = (r : ℝ) := by rw [ht2]; field_simp
  have hplus : ex (ν.iid m) (fun ws => Real.exp (t*S ws)) ≤
      Real.exp (r : ℝ) := by
    simpa only [S, hmt] using iid_bounded_centered_mgf ν m X hcenter hbound t
  have hminus : ex (ν.iid m) (fun ws => Real.exp (-t*S ws)) ≤
      Real.exp (r : ℝ) := by
    simpa only [S, neg_sq, hmt] using
      iid_bounded_centered_mgf ν m X hcenter hbound (-t)
  have hraw := moment_le_of_two_sided_mgf (ν.iid m) S (2*r)
    (by simp : Even (2*r)) t (Real.exp (r : ℝ)) ht hplus hminus
  have hfac : (Nat.factorial (2*r) : ℝ) ≤
      ((r : ℝ)*(r+1))^r := by
    exact_mod_cast factorial_even_le_pair_pow r (by omega)
  have hexp : Real.exp (r : ℝ) ≤ (3 : ℝ)^r := by
    rw [show (r : ℝ) = (r : ℕ)*(1 : ℝ) by simp, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
  have h15 : (2 : ℝ) ≤ (3/2 : ℝ)^r := by
    calc
      (2 : ℝ) ≤ (3/2 : ℝ)^3 := by norm_num
      _ ≤ (3/2 : ℝ)^r := pow_le_pow_right₀ (by norm_num) hr
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hpoly : (9/2 : ℝ)*(r : ℝ)*(r+1) ≤ 2*(r : ℝ)^3 := by
    have hp := mul_nonneg
      (mul_nonneg (le_of_lt hrpos) (by linarith : 0 ≤ (r : ℝ)-3))
      (by linarith : 0 ≤ 2*(r : ℝ)+3/2)
    nlinarith
  have hfacexp :
      2*(Nat.factorial (2*r) : ℝ)*Real.exp (r : ℝ) ≤
        (2*(r : ℝ)^3)^r := by
    calc
      _ ≤ 2*((r : ℝ)*(r+1))^r*(3 : ℝ)^r := by gcongr
      _ = 2*(3*(r : ℝ)*(r+1))^r := by
        calc
          _ = 2*(((r : ℝ)*(r+1))^r*(3 : ℝ)^r) := by ring
          _ = 2*(((r : ℝ)*(r+1))*3)^r := by simp only [mul_pow]
          _ = 2*(3*(r : ℝ)*(r+1))^r := by congr 1; congr 1; ring
      _ ≤ (3/2 : ℝ)^r*(3*(r : ℝ)*(r+1))^r := by
        apply mul_le_mul_of_nonneg_right h15
        positivity
      _ = ((9/2 : ℝ)*(r : ℝ)*(r+1))^r := by
        rw [← mul_pow]
        congr 1
        ring
      _ ≤ (2*(r : ℝ)^3)^r := by gcongr
  have htpow : 0 < t^(2*r) := pow_pos ht _
  have htprod : t^2 * ((r : ℝ)^2*(m : ℝ)) = 2*(r : ℝ)^3 := by
    rw [ht2]
    field_simp
  have hpowequal : t^(2*r) * ((r : ℝ)^2*(m : ℝ))^r =
      (2*(r : ℝ)^3)^r := by
    calc
      _ = (t^2)^r * ((r : ℝ)^2*(m : ℝ))^r := by rw [← pow_mul]
      _ = (t^2*((r : ℝ)^2*(m : ℝ)))^r := (mul_pow _ _ _).symm
      _ = _ := by rw [htprod]
  calc
    _ ≤ 2*(Nat.factorial (2*r) : ℝ)*Real.exp (r : ℝ)/t^(2*r) := hraw
    _ ≤ (2*(r : ℝ)^3)^r/t^(2*r) := by
      exact div_le_div_of_nonneg_right hfacexp htpow.le
    _ = ((r : ℝ)^2*(m : ℝ))^r := by
      apply (div_eq_iff htpow.ne').2
      rw [← hpowequal]
      ring

private theorem expectation_comp_eq_sum_over
    {D C : Type*} [Fintype D]
    (ρ : FiniteLaw D) (u : D → C) (G : C → ℝ)
    (Z : Finset C) (hu : ∀ d, u d ∈ Z) :
    CurrentAdditive.expectation ρ (fun d => G (u d)) =
      ∑ c ∈ Z, G c * ρ.prob (fun d => u d = c) := by
  classical
  unfold CurrentAdditive.expectation FiniteLaw.prob
  calc
    (∑ d, ρ.weight d * G (u d)) =
        ∑ d, ∑ c ∈ Z, if u d = c then ρ.weight d * G c else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      simp [hu d]
    _ = ∑ c ∈ Z, ∑ d,
        if u d = c then ρ.weight d * G c else 0 := Finset.sum_comm
    _ = ∑ c ∈ Z, G c * ∑ d,
        if u d = c then ρ.weight d else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      split_ifs <;> ring

/-- Equality of every event probability for finite sample spaces implies
equality of expectations of every real statistic of the observed value.
The observed value type itself need not be finite. -/
private theorem expectation_comp_eq_of_event_eq
    {A B C : Type*} [Fintype A] [Fintype B]
    (μ : FiniteLaw A) (ν : FiniteLaw B)
    (f : A → C) (g : B → C)
    (hlaw : ∀ E : C → Prop,
      μ.prob (fun a => E (f a)) = ν.prob (fun b => E (g b)))
    (G : C → ℝ) :
    CurrentAdditive.expectation μ (fun a => G (f a)) =
      CurrentAdditive.expectation ν (fun b => G (g b)) := by
  classical
  let Z : Finset C := (Finset.univ.image f) ∪ (Finset.univ.image g)
  have hf : ∀ a, f a ∈ Z := by
    intro a
    exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩))
  have hg : ∀ b, g b ∈ Z := by
    intro b
    exact Finset.mem_union.mpr
      (Or.inr (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩))
  calc
    _ = ∑ c ∈ Z, G c * μ.prob (fun a => f a = c) :=
      expectation_comp_eq_sum_over μ f G Z hf
    _ = ∑ c ∈ Z, G c * ν.prob (fun b => g b = c) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [hlaw (fun z => z = c)]
    _ = _ := (expectation_comp_eq_sum_over ν g G Z hg).symm

/-- Event-law definition of `R`-wise independence for a finite family of
real random variables. The comparison law draws each original carrier
independently, allowing different `X i` functions and marginals. -/
def JointLawAgreement (ν : FiniteLaw Ω) {m : ℕ}
    (X : Fin m → Ω → ℝ) (R : ℕ) : Prop :=
  ∀ s : Finset (Fin m), s.card ≤ R → ∀ E : (s → ℝ) → Prop,
    ν.prob (fun ω => E (fun i : s => X i ω)) =
      (ν.iid m).prob (fun ws => E (fun i : s => X i (ws i)))

/-- An even moment is determined by `2r`-wise joint laws, including terms
with repeated indices. This derives moment transfer from event equality
rather than postulating the target moment as an independence certificate. -/
theorem bounded_wise_raw_moment_eq_iid
    (ν : FiniteLaw Ω) {m r : ℕ} (X : Fin m → Ω → ℝ)
    (hjoint : JointLawAgreement ν X (2*r)) :
    ex ν (fun ω => (∑ i : Fin m, X i ω)^(2*r)) =
      ex (ν.iid m) (fun ws => (∑ i : Fin m, X i (ws i))^(2*r)) := by
  classical
  have hterm (k : Fin (2*r) → Fin m) :
      ex ν (fun ω => ∏ j : Fin (2*r), X (k j) ω) =
        ex (ν.iid m) (fun ws => ∏ j : Fin (2*r), X (k j) (ws (k j))) := by
    let s : Finset (Fin m) := Finset.univ.image k
    have hs : s.card ≤ 2*r := by
      simpa [s] using (Finset.card_image_le (s := Finset.univ) (f := k))
    have hmem (j : Fin (2*r)) : k j ∈ s :=
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    let G : (s → ℝ) → ℝ := fun y => ∏ j : Fin (2*r), y ⟨k j, hmem j⟩
    simpa only [G, ex, CurrentAdditive.expectation] using
      expectation_comp_eq_of_event_eq ν (ν.iid m)
        (fun ω (i : s) => X i ω)
        (fun ws (i : s) => X i (ws i))
        (hjoint s hs) G
  unfold ex
  simp_rw [Fintype.sum_pow]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simpa only [ex] using hterm k

/-- Exact v38 moment inequality for arbitrary bounded centered real
variables in all half-orders at least three, under genuine `2r`-wise event
law agreement on the original finite distribution. -/
theorem bounded_wise_even_moment_ge_three
    (ν : FiniteLaw Ω) (m r : ℕ) (hr : 3 ≤ r)
    (X : Fin m → Ω → ℝ)
    (hcenter : ∀ i, ex ν (X i) = 0)
    (hbound : ∀ i ω, |X i ω| ≤ 1)
    (hjoint : JointLawAgreement ν X (2*r)) :
    ex ν (fun ω => |∑ i : Fin m, X i ω|^(2*r)) ≤
      (((r : ℝ)^2) * m)^r := by
  have hraw := bounded_wise_raw_moment_eq_iid ν X hjoint
  have habs (x : ℝ) : |x|^(2*r) = x^(2*r) :=
    (show Even (2*r) by simp).pow_abs x
  calc
    _ = ex ν (fun ω => (∑ i : Fin m, X i ω)^(2*r)) := by
      congr 1
      funext ω
      exact habs _
    _ = ex (ν.iid m) (fun ws =>
        (∑ i : Fin m, X i (ws i))^(2*r)) := hraw
    _ = ex (ν.iid m) (fun ws =>
        |∑ i : Fin m, X i (ws i)|^(2*r)) := by
          congr 1
          funext ws
          exact (habs _).symm
    _ ≤ _ := iid_bounded_centered_even_moment_ge_three
      ν m r hr X hcenter hbound

#print axioms bounded_centered_mgf
#print axioms iid_bounded_centered_mgf
#print axioms iid_bounded_centered_even_moment_ge_three
#print axioms bounded_wise_even_moment_ge_three

end V38GeneralMoment
