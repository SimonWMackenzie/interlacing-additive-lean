import Paper2.FiniteSampling

/-!
Private proof packet for v27, H-deterministic-core.tex, `det:conditioning`.
The event-restricted Hölder step is proved from the actual finite law.
The even-moment estimate used later is deliberately a separate hypothesis.
-/

namespace CurrentAdditive

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

/-- Finite expectation under a normalized, nonnegative law. -/
noncomputable def expectation (ν : Paper2.FiniteLaw Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, ν.weight ω * X ω

/-- The unnormalized expectation restricted to an event. -/
noncomputable def eventExpectation (ν : Paper2.FiniteLaw Ω)
    (Y : Ω → Prop) (X : Ω → ℝ) : ℝ :=
  by
    classical
    exact ∑ ω, if Y ω then ν.weight ω * X ω else 0

private theorem holder_weight (w : ℝ) (hw : 0 ≤ w)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    w ^ (1 / p) * w ^ (1 / q) = w := by
  rw [← Real.rpow_add' hw (by rw [hpq.one_div_add_one_div]; norm_num)]
  rw [hpq.one_div_add_one_div]
  simp

/-- Exact finite Hölder step for conditioning. The sum on the left uses the
original law, so no conditional-law normalization is hidden. -/
theorem eventExpectation_le_holder (ν : Paper2.FiniteLaw Ω)
    (Y : Ω → Prop) (X : Ω → ℝ) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    eventExpectation ν Y X ≤
      (expectation ν (fun ω => |X ω| ^ p)) ^ (1 / p) *
        (ν.prob Y) ^ (1 / q) := by
  classical
  let f : Ω → ℝ := fun ω => ν.weight ω ^ (1 / p) * X ω
  let g : Ω → ℝ := fun ω => if Y ω then ν.weight ω ^ (1 / q) else 0
  have hleft : eventExpectation ν Y X = ∑ ω, f ω * g ω := by
    unfold eventExpectation
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hY : Y ω
    · simp only [hY, ↓reduceIte, f, g]
      calc
        ν.weight ω * X ω =
            (ν.weight ω ^ (1 / p) * ν.weight ω ^ (1 / q)) * X ω := by
          rw [holder_weight _ (ν.nonneg ω) hpq]
        _ = _ := by ring
    · simp [hY, g]
  have hfirst : ∑ ω, |f ω| ^ p = expectation ν (fun ω => |X ω| ^ p) := by
    unfold expectation
    apply Finset.sum_congr rfl
    intro ω _
    simp only [f, abs_mul, abs_of_nonneg (Real.rpow_nonneg (ν.nonneg ω) _),
      Real.mul_rpow (Real.rpow_nonneg (ν.nonneg ω) _) (abs_nonneg _)]
    rw [← Real.rpow_mul (ν.nonneg ω)]
    have hp : p ≠ 0 := hpq.ne_zero
    rw [show (1 / p) * p = 1 by field_simp]
    simp
  have hsecond : ∑ ω, |g ω| ^ q = ν.prob Y := by
    unfold Paper2.FiniteLaw.prob
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hY : Y ω
    · simp only [hY, ↓reduceIte, g, abs_of_nonneg (Real.rpow_nonneg (ν.nonneg ω) _)]
      rw [← Real.rpow_mul (ν.nonneg ω)]
      have hq : q ≠ 0 := hpq.symm.ne_zero
      rw [show (1 / q) * q = 1 by field_simp]
      simp
    · simp [hY, g, Real.zero_rpow hpq.symm.ne_zero]
  rw [hleft]
  convert Real.inner_le_Lp_mul_Lq (Finset.univ : Finset Ω) f g hpq using 1;
    simp [hfirst, hsecond]

/-- Conditioning is defined only after proving the event has positive mass. -/
noncomputable def condition (ν : Paper2.FiniteLaw Ω) (Y : Ω → Prop)
    (hY : 0 < ν.prob Y) : Paper2.FiniteLaw Ω := by
  classical
  refine {
    weight := fun ω => if Y ω then ν.weight ω / ν.prob Y else 0
    nonneg := ?_
    total := ?_ }
  · intro ω
    split_ifs
    · exact div_nonneg (ν.nonneg ω) hY.le
    · exact le_rfl
  · have hrewrite : (∑ ω, if Y ω then ν.weight ω / ν.prob Y else 0) =
        (∑ ω, if Y ω then ν.weight ω else 0) / ν.prob Y := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ω _
      split_ifs <;> simp
    rw [hrewrite, show (∑ ω, if Y ω then ν.weight ω else 0) = ν.prob Y by rfl,
      div_self hY.ne']

/-- The conditional mean is exactly the restricted original mean divided by
the event mass. -/
theorem condition_expectation (ν : Paper2.FiniteLaw Ω) (Y : Ω → Prop)
    (hY : 0 < ν.prob Y) (X : Ω → ℝ) :
    expectation (condition ν Y hY) X = eventExpectation ν Y X / ν.prob Y := by
  classical
  unfold expectation eventExpectation condition
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : Y ω <;> simp [hω, div_mul_eq_mul_div]

/-- A large conditional mean forces the unconditioned even-moment root to
be large. No independence or concentration estimate is built into this fact. -/
theorem conditional_mean_lt_moment_root (ν : Paper2.FiniteLaw Ω)
    (Y : Ω → Prop) (hY : 0 < ν.prob Y) (X : Ω → ℝ)
    (r : ℝ) (hr : 1 < r) (b : ℝ)
    (hmean : b < expectation (condition ν Y hY) X) :
    ν.prob Y * b <
      (expectation ν (fun ω => |X ω| ^ r)) ^ (1 / r) *
        (ν.prob Y) ^ (1 - 1 / r) := by
  have hpq : r.HolderConjugate (Real.conjExponent r) :=
    Real.HolderConjugate.conjExponent hr
  have hexp : 1 / Real.conjExponent r = 1 - 1 / r := by
    linarith [hpq.one_div_add_one_div]
  have hcond := condition_expectation ν Y hY X
  have hrestricted : ν.prob Y * b < eventExpectation ν Y X := by
    rw [hcond] at hmean
    simpa [mul_comm] using (lt_div_iff₀ hY).mp hmean
  have hholder := eventExpectation_le_holder ν Y X hpq
  rw [hexp] at hholder
  exact hrestricted.trans_le hholder

/-- Algebraic form of the conditioning argument. The event-mass factor is
explicit; `C * sqrt m` is the assumed root-moment bound. -/
private theorem witness_count_algebra
    (θ t u m ε C : ℝ)
    (hθ : θ = t * u) (ht : 0 < t) (hu : 0 < u)
    (hm : 0 < m) (hε : 0 < ε)
    (h : θ * (m * ε) < C * Real.sqrt m * u) :
    m * (ε * t) ^ 2 < C ^ 2 := by
  have hz : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hz2 : (Real.sqrt m) ^ 2 = m := Real.sq_sqrt hm.le
  have h1 : (m * ε * t) * u < (C * Real.sqrt m) * u := by
    calc
      (m * ε * t) * u = θ * (m * ε) := by rw [hθ]; ring
      _ < _ := h
  have h2 : m * ε * t < C * Real.sqrt m :=
    lt_of_mul_lt_mul_right h1 hu.le
  have h3 : Real.sqrt m * (ε * t) < C := by
    have h2' : (Real.sqrt m * (ε * t)) * Real.sqrt m <
        C * Real.sqrt m := by
      calc
        (Real.sqrt m * (ε * t)) * Real.sqrt m =
            (Real.sqrt m) ^ 2 * ε * t := by ring
        _ = m * ε * t := by rw [hz2]
        _ < _ := h2
    exact lt_of_mul_lt_mul_right h2' hz.le
  have hA : 0 ≤ Real.sqrt m * (ε * t) := by positivity
  have hC : 0 < C := lt_of_le_of_lt hA h3
  have hprod : 0 < (C - Real.sqrt m * (ε * t)) *
      (C + Real.sqrt m * (ε * t)) :=
    mul_pos (sub_pos.mpr h3) (add_pos_of_pos_of_nonneg hC hA)
  nlinarith [hprod]

/-- A conditional mean exceeding `m ε` bounds the number `m` of witnesses
once the *unconditioned* root moment has been proved. For the paper the
even order is `r = 1024`; this theorem works at every real order above one. -/
theorem witness_count_of_root_moment (ν : Paper2.FiniteLaw Ω)
    (Y : Ω → Prop) (hY : 0 < ν.prob Y) (S : Ω → ℝ)
    (r : ℝ) (hr : 1 < r) (m : ℕ) (hm : 0 < m) (ε C : ℝ)
    (hε : 0 < ε)
    (hmean : (m : ℝ) * ε < expectation (condition ν Y hY) S)
    (hMomentRoot :
      (expectation ν (fun ω => |S ω| ^ r)) ^ (1 / r) ≤
        C * Real.sqrt m) :
    (m : ℝ) * (ε * (ν.prob Y) ^ (1 / r)) ^ 2 < C ^ 2 := by
  let θ := ν.prob Y
  let t := θ ^ (1 / r)
  let u := θ ^ (1 - 1 / r)
  have ht : 0 < t := Real.rpow_pos_of_pos hY _
  have hu : 0 < u := Real.rpow_pos_of_pos hY _
  have hfactor : θ = t * u := by
    rw [← Real.rpow_add hY]
    simp [θ]
  have hmain := conditional_mean_lt_moment_root ν Y hY S r hr
    ((m : ℝ) * ε) hmean
  have hbounded : θ * ((m : ℝ) * ε) < C * Real.sqrt m * u :=
    hmain.trans_le (mul_le_mul_of_nonneg_right hMomentRoot hu.le)
  exact witness_count_algebra θ t u m ε C hfactor ht hu
    (Nat.cast_pos.mpr hm) hε hbounded

/-- Convert the paper's even-moment estimate to the root form consumed above.
This is only algebra: the moment estimate remains an explicit premise. -/
theorem root_bound_of_even_moment
    (r : ℝ) (hr : 1 < r) (m : ℕ) (M : ℝ)
    (hM0 : 0 ≤ M)
    (hMoment : M ≤ 2 * (r * m / 4) ^ (r / 2)) :
    M ^ (1 / r) ≤
      2 ^ (1 / r) * Real.sqrt (r / 4) * Real.sqrt m := by
  have hr0 : 0 < r := lt_trans (by norm_num) hr
  have hbase : 0 ≤ r * m / 4 := by positivity
  have hquarter : 0 ≤ r / 4 := by positivity
  calc
    M ^ (1 / r) ≤ (2 * (r * m / 4) ^ (r / 2)) ^ (1 / r) :=
      Real.rpow_le_rpow hM0 hMoment (by positivity)
    _ = 2 ^ (1 / r) * ((r * m / 4) ^ (r / 2)) ^ (1 / r) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
        (Real.rpow_nonneg hbase _)]
    _ = 2 ^ (1 / r) * Real.sqrt (r * m / 4) := by
      rw [← Real.rpow_mul hbase]
      have he : r / 2 * (1 / r) = (1 / (2 : ℝ)) := by field_simp
      rw [he, ← Real.sqrt_eq_rpow]
    _ = 2 ^ (1 / r) * Real.sqrt (r / 4) * Real.sqrt m := by
      have hmul : r * m / 4 = (r / 4) * m := by ring
      rw [hmul, Real.sqrt_mul hquarter]
      ring

/-- The precise numerical factor obtained from `det:even-moment` and finite
Hölder. The paper's printed `m < r ε⁻² θ^(-2/r)` is a looser consequence
for its order `r = 1024`. This theorem assumes the even-moment inequality;
it does not prove it from bounded independence. -/
theorem witness_count_of_even_moment (ν : Paper2.FiniteLaw Ω)
    (Y : Ω → Prop) (hY : 0 < ν.prob Y) (S : Ω → ℝ)
    (r : ℝ) (hr : 1 < r) (m : ℕ) (hm : 0 < m) (ε : ℝ)
    (hε : 0 < ε)
    (hmean : (m : ℝ) * ε < expectation (condition ν Y hY) S)
    (hMoment : expectation ν (fun ω => |S ω| ^ r) ≤
      2 * (r * m / 4) ^ (r / 2)) :
    (m : ℝ) * (ε * (ν.prob Y) ^ (1 / r)) ^ 2 <
      2 ^ (2 / r) * (r / 4) := by
  have hM0 : 0 ≤ expectation ν (fun ω => |S ω| ^ r) := by
    unfold expectation
    exact Finset.sum_nonneg fun ω _ =>
      mul_nonneg (ν.nonneg ω) (Real.rpow_nonneg (abs_nonneg _) _)
  have hroot := root_bound_of_even_moment r hr m
    (expectation ν (fun ω => |S ω| ^ r)) hM0 hMoment
  have hmain := witness_count_of_root_moment ν Y hY S r hr m hm ε
    (2 ^ (1 / r) * Real.sqrt (r / 4)) hε hmean hroot
  have hr0 : 0 ≤ r / 4 := by positivity
  have hconst : (2 ^ (1 / r) * Real.sqrt (r / 4)) ^ 2 =
      2 ^ (2 / r) * (r / 4) := by
    rw [mul_pow, Real.sq_sqrt hr0, ← Real.rpow_two,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    field_simp
  rwa [hconst] at hmain

/-- A direct `m` bound at every even order at least two. This is the paper's
bound with the reciprocal factors kept as one positive denominator. -/
theorem witness_count_lt_div_of_even_moment (ν : Paper2.FiniteLaw Ω)
    (Y : Ω → Prop) (hY : 0 < ν.prob Y) (S : Ω → ℝ)
    (r : ℝ) (hr : 2 ≤ r) (m : ℕ) (hm : 0 < m) (ε : ℝ)
    (hε : 0 < ε)
    (hmean : (m : ℝ) * ε < expectation (condition ν Y hY) S)
    (hMoment : expectation ν (fun ω => |S ω| ^ r) ≤
      2 * (r * m / 4) ^ (r / 2)) :
    (m : ℝ) < r / (ε * (ν.prob Y) ^ (1 / r)) ^ 2 := by
  have hr1 : 1 < r := lt_of_lt_of_le (by norm_num) hr
  have hstrong := witness_count_of_even_moment ν Y hY S r hr1 m hm ε
    hε hmean hMoment
  have hexp : 2 / r ≤ (1 : ℝ) := (div_le_iff₀ (by linarith)).2 (by linarith)
  have hpow : 2 ^ (2 / r) ≤ (2 : ℝ) := by
    simpa using Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 2) hexp
  have hr0 : 0 ≤ r := by linarith
  have hsmall : 2 ^ (2 / r) * (r / 4) ≤ r := by
    nlinarith [mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ r / 4)]
  have hscaled : (m : ℝ) * (ε * (ν.prob Y) ^ (1 / r)) ^ 2 < r :=
    hstrong.trans_le hsmall
  have hden : 0 < (ε * (ν.prob Y) ^ (1 / r)) ^ 2 := by positivity
  exact (lt_div_iff₀ hden).2 hscaled

/-- The same count in the notation of `det:conditioning`: the factor
`ε⁻² θ^(-2/r)` is derived here rather than silently identified with the
positive denominator in the preceding theorem. -/
theorem witness_count_lt_paper_form (ν : Paper2.FiniteLaw Ω)
    (Y : Ω → Prop) (hY : 0 < ν.prob Y) (S : Ω → ℝ)
    (r : ℝ) (hr : 2 ≤ r) (m : ℕ) (hm : 0 < m) (ε : ℝ)
    (hε : 0 < ε)
    (hmean : (m : ℝ) * ε < expectation (condition ν Y hY) S)
    (hMoment : expectation ν (fun ω => |S ω| ^ r) ≤
      2 * (r * m / 4) ^ (r / 2)) :
    (m : ℝ) < r * ε ^ (-(2 : ℝ)) * (ν.prob Y) ^ (-(2 / r)) := by
  have hbound := witness_count_lt_div_of_even_moment ν Y hY S r hr m hm ε
    hε hmean hMoment
  have hr0 : 0 < r := by linarith
  have hden : (ε * (ν.prob Y) ^ (1 / r)) ^ 2 =
      ε ^ 2 * (ν.prob Y) ^ (2 / r) := by
    have ht : ((ν.prob Y) ^ (1 / r)) ^ 2 =
        (ν.prob Y) ^ (2 / r) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hY.le]
      congr 1
      field_simp
    rw [mul_pow, ht]
  have hform : r / (ε * (ν.prob Y) ^ (1 / r)) ^ 2 =
      r * ε ^ (-(2 : ℝ)) * (ν.prob Y) ^ (-(2 / r)) := by
    rw [hden, div_eq_mul_inv, mul_inv_rev,
      Real.rpow_neg hε.le, Real.rpow_two, Real.rpow_neg hY.le]
    ring
  rw [hform] at hbound
  exact hbound

/-- Replace the actual event mass by the lower bound `v` used in v27.
The direction is important: a smaller conditioning event allows a larger
exceptional family. -/
theorem witness_count_lt_mass_lower_bound (ν : Paper2.FiniteLaw Ω)
    (Y : Ω → Prop) (v : ℝ) (hv : 0 < v) (hvY : v ≤ ν.prob Y)
    (S : Ω → ℝ) (r : ℝ) (hr : 2 ≤ r)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hmean : (m : ℝ) * ε <
      expectation (condition ν Y (lt_of_lt_of_le hv hvY)) S)
    (hMoment : expectation ν (fun ω => |S ω| ^ r) ≤
      2 * (r * m / 4) ^ (r / 2)) :
    (m : ℝ) < r * ε ^ (-(2 : ℝ)) * v ^ (-(2 / r)) := by
  have hY : 0 < ν.prob Y := lt_of_lt_of_le hv hvY
  have hbound := witness_count_lt_paper_form ν Y hY S r hr m hm ε hε
    hmean hMoment
  have hexp : -(2 / r) ≤ 0 := by
    have : 0 < r := by linarith
    exact neg_nonpos.mpr (div_nonneg (by norm_num) this.le)
  have hpow : (ν.prob Y) ^ (-(2 / r)) ≤ v ^ (-(2 / r)) :=
    Real.rpow_le_rpow_of_nonpos hv hvY hexp
  have hfactor : 0 ≤ r * ε ^ (-(2 : ℝ)) := by positivity
  exact hbound.trans_le (mul_le_mul_of_nonneg_left hpow hfactor)

/-- Finite expectation commutes with a finite sum without any independence. -/
theorem expectation_sum (ν : Paper2.FiniteLaw Ω)
    {ι : Type*} (s : Finset ι) (F : ι → Ω → ℝ) :
    expectation ν (fun ω => ∑ i ∈ s, F i ω) =
      ∑ i ∈ s, expectation ν (F i) := by
  classical
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem expectation_sub_const (ν : Paper2.FiniteLaw Ω)
    (F : Ω → ℝ) (c : ℝ) :
    expectation ν (fun ω => F ω - c) = expectation ν F - c := by
  classical
  unfold expectation
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ν.total, one_mul]

/-- The original expectation of a centered function is zero. -/
theorem expectation_sub_own_mean (ν : Paper2.FiniteLaw Ω)
    (F : Ω → ℝ) :
    expectation ν (fun ω => F ω - expectation ν F) = 0 := by
  classical
  unfold expectation
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ν.total, one_mul]
  ring

/-- A pointwise discrepancy on `m` bounded indicator tests gives a large
conditional mean for their centered sum. The tests are represented by
predicates, hence take only values zero and one. -/
theorem centered_indicator_sum_large_mean (ν : Paper2.FiniteLaw Ω)
    (Y : Ω → Prop) (hY : 0 < ν.prob Y) (m : ℕ) (hm : 0 < m)
    (F : Fin m → Ω → Bool) (ε : ℝ)
    (hdiscrepancy : ∀ i : Fin m,
      ε < expectation (condition ν Y hY)
            (fun ω => if F i ω then (1 : ℝ) else 0) -
          expectation ν (fun ω => if F i ω then (1 : ℝ) else 0)) :
    (m : ℝ) * ε <
      expectation (condition ν Y hY) (fun ω =>
        ∑ i : Fin m, ((if F i ω then (1 : ℝ) else 0) -
          expectation ν (fun ω' => if F i ω' then (1 : ℝ) else 0))) := by
  classical
  let f : Fin m → Ω → ℝ := fun i ω => if F i ω then 1 else 0
  have hsum : (∑ i : Fin m, ε) <
      ∑ i : Fin m,
        (expectation (condition ν Y hY) (f i) - expectation ν (f i)) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact (hdiscrepancy i).le
    · exact ⟨⟨0, hm⟩, Finset.mem_univ _, hdiscrepancy ⟨0, hm⟩⟩
  have htarget : (m : ℝ) * ε <
      expectation (condition ν Y hY) (fun ω =>
        ∑ i : Fin m, (f i ω - expectation ν (f i))) := by
    rw [expectation_sum]
    simpa only [expectation_sub_const, Finset.sum_const_zero,
      Finset.sum_const, Finset.card_fin, nsmul_eq_mul] using hsum
  simpa only [f] using htarget

/-- Indicator-test version of the paper's conditioning count. The Boolean
tests are automatically bounded by zero and one. Independence is needed to
prove `hEvenMoment` in a later module; here it is exposed as exactly the
remaining analytical premise. -/
theorem indicator_witness_count_of_even_moment (ν : Paper2.FiniteLaw Ω)
    (Y : Ω → Prop) (hY : 0 < ν.prob Y)
    (r : ℝ) (hr : 2 ≤ r) (m : ℕ) (hm : 0 < m)
    (F : Fin m → Ω → Bool) (ε : ℝ) (hε : 0 < ε)
    (hdiscrepancy : ∀ i : Fin m,
      ε < expectation (condition ν Y hY)
            (fun ω => if F i ω then (1 : ℝ) else 0) -
          expectation ν (fun ω => if F i ω then (1 : ℝ) else 0))
    (hEvenMoment :
      expectation ν (fun ω =>
        |∑ i : Fin m, ((if F i ω then (1 : ℝ) else 0) -
          expectation ν (fun ω' => if F i ω' then (1 : ℝ) else 0))| ^ r) ≤
        2 * (r * m / 4) ^ (r / 2)) :
    (m : ℝ) < r / (ε * (ν.prob Y) ^ (1 / r)) ^ 2 := by
  let S : Ω → ℝ := fun ω =>
    ∑ i : Fin m, ((if F i ω then (1 : ℝ) else 0) -
      expectation ν (fun ω' => if F i ω' then (1 : ℝ) else 0))
  have hmean : (m : ℝ) * ε < expectation (condition ν Y hY) S :=
    centered_indicator_sum_large_mean ν Y hY m hm F ε hdiscrepancy
  exact witness_count_lt_div_of_even_moment ν Y hY S r hr m hm ε hε
    hmean hEvenMoment

/-- A proved second-moment expansion for pairwise uncorrelated summands.
This is a genuine even-moment calculation, but it is only order two; the
paper needs the order-1024 estimate for its rare-event exponent. -/
theorem second_moment_of_uncorrelated (ν : Paper2.FiniteLaw Ω)
    (m : ℕ) (X : Fin m → Ω → ℝ)
    (hdiag : ∀ i : Fin m,
      expectation ν (fun ω => (X i ω) ^ 2) ≤ 1 / 4)
    (hcross : ∀ i j : Fin m, i ≠ j →
      expectation ν (fun ω => X i ω * X j ω) = 0) :
    expectation ν (fun ω => (∑ i : Fin m, X i ω) ^ 2) ≤ m / 4 := by
  classical
  have hsquare (ω : Ω) :
      (∑ i : Fin m, X i ω) ^ 2 =
        ∑ i : Fin m, ∑ j : Fin m, X i ω * X j ω := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have hmove : expectation ν (fun ω =>
      ∑ i : Fin m, ∑ j : Fin m, X i ω * X j ω) =
      ∑ i : Fin m, ∑ j : Fin m,
        expectation ν (fun ω => X i ω * X j ω) := by
    rw [expectation_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [expectation_sum]
  have hcollapse :
      (∑ i : Fin m, ∑ j : Fin m,
        expectation ν (fun ω => X i ω * X j ω)) =
      ∑ i : Fin m, expectation ν (fun ω => (X i ω) ^ 2) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · congr 1
      funext ω
      ring
    · intro j _ hij
      exact hcross i j (Ne.symm hij)
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  calc
    expectation ν (fun ω => (∑ i : Fin m, X i ω) ^ 2) =
        expectation ν (fun ω =>
          ∑ i : Fin m, ∑ j : Fin m, X i ω * X j ω) := by
      congr 1
      funext ω
      exact hsquare ω
    _ = ∑ i : Fin m, expectation ν (fun ω => (X i ω) ^ 2) := by
      rw [hmove, hcollapse]
    _ ≤ ∑ _i : Fin m, (1 / 4 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact hdiag i
    _ = m / 4 := by simp; ring

end CurrentAdditive

#print axioms CurrentAdditive.eventExpectation_le_holder
#print axioms CurrentAdditive.witness_count_lt_mass_lower_bound
#print axioms CurrentAdditive.indicator_witness_count_of_even_moment
#print axioms CurrentAdditive.second_moment_of_uncorrelated
