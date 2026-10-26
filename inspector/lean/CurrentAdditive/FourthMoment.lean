import CurrentAdditive.IndependentStreams

/-!
Private Appendix H probe for `det:fourth-moment` and `det:exact-pair-tail`.
The carrier of a source law is kept indexed.  The cross-moment hypotheses in
`fourth_bound_of_cross_moments` are the explicit identities to derive from
eight-wise original-coordinate marginals; they are not a fourth-moment bound.
-/

namespace CurrentAdditive.FourthMoment

open Paper2
open scoped BigOperators

variable {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]

noncomputable def expect (ν : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, ν.weight ω * f ω

theorem expect_add (ν : FiniteLaw Ω) (f g : Ω → ℝ) :
    expect ν (fun ω => f ω + g ω) = expect ν f + expect ν g := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

theorem expect_mul_const (ν : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    expect ν (fun ω => c * f ω) = c * expect ν f := by
  unfold expect
  calc
    (∑ ω, ν.weight ω * (c * f ω)) = ∑ ω, c * (ν.weight ω * f ω) := by
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = c * ∑ ω, ν.weight ω * f ω := (Finset.mul_sum _ _ _).symm

theorem expect_sub (ν : FiniteLaw Ω) (f g : Ω → ℝ) :
    expect ν (fun ω => f ω - g ω) = expect ν f - expect ν g := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_nonneg (ν : FiniteLaw Ω) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ expect ν f := by
  exact Finset.sum_nonneg (fun ω _ => mul_nonneg (ν.nonneg ω) (hf ω))

theorem expect_le (ν : FiniteLaw Ω) (f g : Ω → ℝ)
    (hfg : ∀ ω, f ω ≤ g ω) : expect ν f ≤ expect ν g := by
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (hfg ω) (ν.nonneg ω)

theorem expect_one (ν : FiniteLaw Ω) : expect ν (fun _ => 1) = 1 := by
  simpa [expect] using ν.total

theorem expect_sum {J : Type*} (ν : FiniteLaw Ω) (s : Finset J)
    (f : J → Ω → ℝ) :
    expect ν (fun ω => ∑ j ∈ s, f j ω) = ∑ j ∈ s, expect ν (f j) := by
  unfold expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem expect_indicator (ν : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] :
    expect ν (fun ω => if E ω then (1 : ℝ) else 0) = ν.prob E := by
  unfold expect FiniteLaw.prob
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : E ω <;> simp [h]

theorem expect_centered_indicator (ν : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] :
    expect ν (fun ω => (if E ω then (1 : ℝ) else 0) - ν.prob E) = 0 := by
  rw [expect_sub, expect_indicator]
  have hc : expect ν (fun _ => ν.prob E) = ν.prob E := by
    convert expect_mul_const ν (fun _ => 1) (ν.prob E) using 1 <;>
      simp [expect_one]
  rw [hc]
  ring

/-- Exact single-Bernoulli second moment. -/
theorem centered_indicator_second (ν : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] :
    expect ν (fun ω => ((if E ω then (1 : ℝ) else 0) - ν.prob E)^2) =
      ν.prob E * (1 - ν.prob E) := by
  let p := ν.prob E
  let Z : Ω → ℝ := fun ω => if E ω then 1 else 0
  have hpoint (ω : Ω) : (Z ω - p)^2 = Z ω * (1 - 2*p) + p^2 := by
    by_cases h : E ω <;> simp [Z, h] <;> ring
  calc
    _ = expect ν (fun ω => Z ω * (1 - 2*p) + p^2) := by
      congr 1
      funext ω
      exact hpoint ω
    _ = p * (1-p) := by
      rw [expect_add]
      have hz : expect ν Z = p := expect_indicator ν E
      have ha : expect ν (fun ω => Z ω * (1 - 2*p)) = p * (1 - 2*p) := by
        convert expect_mul_const ν Z (1 - 2*p) using 1
        · congr 1; funext ω; ring
        · rw [hz]; ring
      have hb : expect ν (fun _ => p^2) = p^2 := by
        convert expect_mul_const ν (fun _ => 1) (p^2) using 1 <;>
          simp [expect_one]
      rw [ha, hb]
      ring

theorem centered_indicator_second_le_quarter (ν : FiniteLaw Ω) (E : Ω → Prop)
    [DecidablePred E] :
    expect ν (fun ω => ((if E ω then (1 : ℝ) else 0) - ν.prob E)^2) ≤ 1/4 := by
  rw [centered_indicator_second]
  nlinarith [sq_nonneg (ν.prob E - 1/2)]

/-- The fourth power of a centered Bernoulli variable is at most its
second power, pointwise; hence its mean is at most one quarter. -/
theorem centered_indicator_fourth_le_quarter (ν : FiniteLaw Ω) (E : Ω → Prop)
    [DecidablePred E] :
    expect ν (fun ω => ((if E ω then (1 : ℝ) else 0) - ν.prob E)^4) ≤ 1/4 := by
  have hp0 := ν.prob_nonneg E
  have hp1 := ν.prob_le_one E
  calc
    _ ≤ expect ν (fun ω => ((if E ω then (1 : ℝ) else 0) - ν.prob E)^2) := by
      apply expect_le
      intro ω
      by_cases hE : E ω
      · simp only [hE, ↓reduceIte]
        have hx : (1 - ν.prob E)^2 ≤ 1 := by nlinarith
        nlinarith [mul_nonneg (sq_nonneg (1 - ν.prob E)) (sub_nonneg.mpr hx)]
      · simp only [hE, ↓reduceIte, zero_sub]
        have hx : (ν.prob E)^2 ≤ 1 := by nlinarith
        nlinarith [mul_nonneg (sq_nonneg (ν.prob E)) (sub_nonneg.mpr hx)]
    _ ≤ 1/4 := centered_indicator_second_le_quarter ν E

def sumCentered (X : I → Ω → ℝ) (s : Finset I) (ω : Ω) : ℝ :=
  ∑ i ∈ s, X i ω

/-- Ordered-term expansion used by the manuscript's conditioning error:
there are exactly `m⁴` summands when the index carrier has `m` members. -/
theorem fourth_expand (ν : FiniteLaw Ω) (X : I → Ω → ℝ) (s : Finset I) :
    expect ν (fun ω => (sumCentered X s ω)^4) =
      ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, ∑ l ∈ s,
        expect ν (fun ω => X l ω * X k ω * X j ω * X i ω) := by
  have hpoint (ω : Ω) : (sumCentered X s ω)^4 =
      ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, ∑ l ∈ s,
        X l ω * X k ω * X j ω * X i ω := by
    simp only [sumCentered]
    calc
      (∑ i ∈ s, X i ω)^4 =
          (∑ i ∈ s, X i ω) * (∑ j ∈ s, X j ω) *
          (∑ k ∈ s, X k ω) * (∑ l ∈ s, X l ω) := by ring
      _ = _ := by
        simp only [Finset.sum_mul, Finset.mul_sum]
  simp_rw [hpoint, expect_sum]

/-- An actual finite conditional law on the original indexed carrier. -/
noncomputable def conditional (ν : FiniteLaw Ω) (Y : Ω → Prop)
    [DecidablePred Y] (hY : 0 < ν.prob Y) : FiniteLaw Ω where
  weight ω := if Y ω then ν.weight ω / ν.prob Y else 0
  nonneg ω := by
    split_ifs
    · exact div_nonneg (ν.nonneg ω) hY.le
    · exact le_refl 0
  total := by
    change (∑ ω, if Y ω then ν.weight ω / ν.prob Y else 0) = 1
    calc
      _ = (∑ ω, if Y ω then ν.weight ω else 0) / ν.prob Y := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro ω _
        by_cases h : Y ω <;> simp [h]
      _ = 1 := by
        have hsum : (∑ ω, if Y ω then ν.weight ω else 0) = ν.prob Y := by
          unfold FiniteLaw.prob
          apply Finset.sum_congr rfl
          intro ω _
          by_cases h : Y ω <;> simp [h]
        rw [hsum]
        exact div_self hY.ne'

theorem conditional_prob (ν : FiniteLaw Ω) (Y K : Ω → Prop)
    [DecidablePred Y] (hY : 0 < ν.prob Y) (hK : ∀ ω, K ω → Y ω) :
    (conditional ν Y hY).prob K = ν.prob K / ν.prob Y := by
  classical
  change (∑ ω, if K ω then (if Y ω then ν.weight ω / ν.prob Y else 0) else 0) =
    (∑ ω, if K ω then ν.weight ω else 0) / ν.prob Y
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hk : K ω
  · simp [hk, hK ω hk]
  · simp [hk]

/-- Finite-law fourth-moment recurrence.  These three cross identities are
the algebraic consequences of four-wise independence and centering; no
bound on the final sum is a premise. -/
theorem fourth_bound_of_cross_moments (ν : FiniteLaw Ω) (X : I → Ω → ℝ)
    (hsecond : ∀ i, expect ν (fun ω => (X i ω)^2) ≤ 1/4)
    (hfourth : ∀ i, expect ν (fun ω => (X i ω)^4) ≤ 1/4)
    (hcross1 : ∀ (s : Finset I) (i : I), i ∉ s →
      expect ν (fun ω => sumCentered X s ω * X i ω) = 0)
    (hcross31 : ∀ (s : Finset I) (i : I), i ∉ s →
      expect ν (fun ω => (sumCentered X s ω)^3 * X i ω) = 0)
    (hcross13 : ∀ (s : Finset I) (i : I), i ∉ s →
      expect ν (fun ω => sumCentered X s ω * (X i ω)^3) = 0)
    (hcross22 : ∀ (s : Finset I) (i : I), i ∉ s →
      expect ν (fun ω => (sumCentered X s ω)^2 * (X i ω)^2) =
        expect ν (fun ω => (sumCentered X s ω)^2) *
          expect ν (fun ω => (X i ω)^2))
    (s : Finset I) :
    expect ν (fun ω => (sumCentered X s ω)^2) ≤ (s.card : ℝ)/4 ∧
    expect ν (fun ω => (sumCentered X s ω)^4) ≤
      (s.card : ℝ)/4 + 3 * (s.card : ℝ)^2 / 16 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [sumCentered, expect]
  | @insert i s hi ih =>
      obtain ⟨ih2, ih4⟩ := ih
      have hs (ω : Ω) : sumCentered X (insert i s) ω = sumCentered X s ω + X i ω := by
        simp [sumCentered, Finset.sum_insert hi, add_comm]
      have hm2 : expect ν (fun ω => (sumCentered X (insert i s) ω)^2) =
          expect ν (fun ω => (sumCentered X s ω)^2) +
            expect ν (fun ω => (X i ω)^2) := by
        simp_rw [hs]
        have heq : (fun ω => (sumCentered X s ω + X i ω)^2) =
            (fun ω => (sumCentered X s ω)^2 + 2 *
              (sumCentered X s ω * X i ω) + (X i ω)^2) := by
          funext ω; ring
        rw [heq, expect_add, expect_add, expect_mul_const, hcross1 s i hi]
        ring
      have hm4 : expect ν (fun ω => (sumCentered X (insert i s) ω)^4) =
          expect ν (fun ω => (sumCentered X s ω)^4) +
            6 * expect ν (fun ω => (sumCentered X s ω)^2) *
              expect ν (fun ω => (X i ω)^2) +
            expect ν (fun ω => (X i ω)^4) := by
        simp_rw [hs]
        have heq : (fun ω => (sumCentered X s ω + X i ω)^4) =
            (fun ω => (sumCentered X s ω)^4 +
              4 * ((sumCentered X s ω)^3 * X i ω) +
              6 * ((sumCentered X s ω)^2 * (X i ω)^2) +
              4 * (sumCentered X s ω * (X i ω)^3) +
              (X i ω)^4) := by
          funext ω; ring
        rw [heq]
        repeat rw [expect_add]
        repeat rw [expect_mul_const]
        rw [hcross31 s i hi, hcross13 s i hi, hcross22 s i hi]
        ring
      constructor
      · rw [hm2, Finset.card_insert_of_notMem hi]
        have := hsecond i
        push_cast
        linarith
      · rw [hm4, Finset.card_insert_of_notMem hi]
        have hvar0 : 0 ≤ expect ν (fun ω => (sumCentered X s ω)^2) :=
          expect_nonneg ν _ (fun ω => sq_nonneg _)
        have hvari0 : 0 ≤ expect ν (fun ω => (X i ω)^2) :=
          expect_nonneg ν _ (fun ω => sq_nonneg _)
        have hvari := hsecond i
        have h4i := hfourth i
        have hprod : expect ν (fun ω => (sumCentered X s ω)^2) *
            expect ν (fun ω => (X i ω)^2) ≤ ((s.card : ℝ)/4) * (1/4) :=
          mul_le_mul ih2 hvari hvari0 (by positivity)
        push_cast
        nlinarith

/-- Fourth-power Markov step for an event on which the centered sum is
large. The event may be an arbitrary subset of the indexed source carrier. -/
theorem event_le_fourth_moment (ν : FiniteLaw Ω) (S : Ω → ℝ)
    (K : Ω → Prop) (a : ℝ) (ha : 0 < a)
    (hK : ∀ ω, K ω → a ≤ S ω) :
    a^4 * ν.prob K ≤ expect ν (fun ω => (S ω)^4) := by
  classical
  unfold FiniteLaw.prob expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : K ω
  · simp only [h, ↓reduceIte]
    have hpow : a^4 ≤ (S ω)^4 := pow_le_pow_left₀ ha.le (hK ω h) 4
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hpow (ν.nonneg ω)
  · simp only [h, ↓reduceIte, mul_zero]
    exact mul_nonneg (ν.nonneg ω) (Even.pow_nonneg (by decide : Even 4) _)

/-- The manuscript's strict `9/(50m)` numerical comparison for `m ≥ 8`. -/
theorem exact_pair_numeric (m : ℝ) (hm : 8 ≤ m) :
    (m/4 + 3*m^2/16) / ((16/25 : ℝ)^4 * m^4) < 9/(50*m) := by
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m^2 := pow_pos hm0 _
  have hm3 : 0 < m^3 := pow_pos hm0 _
  have hm4 : 0 < m^4 := pow_pos hm0 _
  have hlinear : 8*m ≤ m^2 := by nlinarith [mul_nonneg hm0.le (sub_nonneg.mpr hm)]
  have hcubic : 8*m^2 ≤ m^3 := by nlinarith [mul_nonneg hm2.le (sub_nonneg.mpr hm)]
  have hquartic : 8*m^3 ≤ m^4 := by nlinarith [mul_nonneg hm3.le (sub_nonneg.mpr hm)]
  apply (div_lt_iff₀ (by positivity : 0 < (16/25 : ℝ)^4 * m^4)).2
  have hright : 9/(50*m) * ((16/25 : ℝ)^4 * m^4) =
      (9/50 : ℝ) * ((16/25 : ℝ)^4) * m^3 := by
    field_simp
  rw [hright]
  norm_num at *
  nlinarith

/-- For `m ≥ 16` the same fourth-moment term is below `1/(8m)`. -/
theorem moderate_pair_numeric (m : ℝ) (hm : 16 ≤ m) :
    (m/4 + 3*m^2/16) / ((16/25 : ℝ)^4 * m^4) < 1/(8*m) := by
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m^2 := pow_pos hm0 _
  have hm3 : 0 < m^3 := pow_pos hm0 _
  have hm4 : 0 < m^4 := pow_pos hm0 _
  have hlinear : 16*m ≤ m^2 := by nlinarith [mul_nonneg hm0.le (sub_nonneg.mpr hm)]
  have hcubic : 16*m^2 ≤ m^3 := by nlinarith [mul_nonneg hm2.le (sub_nonneg.mpr hm)]
  have hquartic : 16*m^3 ≤ m^4 := by nlinarith [mul_nonneg hm3.le (sub_nonneg.mpr hm)]
  apply (div_lt_iff₀ (by positivity : 0 < (16/25 : ℝ)^4 * m^4)).2
  have hright : 1/(8*m) * ((16/25 : ℝ)^4 * m^4) =
      (1/8 : ℝ) * ((16/25 : ℝ)^4) * m^3 := by
    field_simp
  rw [hright]
  norm_num at *
  nlinarith

/-- Accumulating the `m⁴` bounded differences of the ordered quartic
terms.  The termwise premise is exactly what a good eight-coordinate
total-variation estimate must supply; it does not assume the conclusion. -/
theorem fourth_difference_of_terms
    {Ψ : Type*} [Fintype Ψ]
    (ν : FiniteLaw Ω) (ρ : FiniteLaw Ψ) (decode : Ω → Ψ)
    (X : I → Ψ → ℝ) (s : Finset I) (ε : ℝ)
    (hterm : ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s, ∀ l ∈ s,
      expect ν (fun ω => X l (decode ω) * X k (decode ω) *
        X j (decode ω) * X i (decode ω)) ≤
      expect ρ (fun ψ => X l ψ * X k ψ * X j ψ * X i ψ) + 2*ε) :
    expect ν (fun ω => (∑ i ∈ s, X i (decode ω))^4) ≤
      expect ρ (fun ψ => (∑ i ∈ s, X i ψ)^4) +
        2*ε*(s.card : ℝ)^4 := by
  change expect ν (fun ω => (sumCentered (fun i ω => X i (decode ω)) s ω)^4) ≤
    expect ρ (fun ψ => (sumCentered X s ψ)^4) + 2*ε*(s.card : ℝ)^4
  rw [fourth_expand ν (fun i ω => X i (decode ω)) s,
    fourth_expand ρ X s]
  have hsum :
      (∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, ∑ l ∈ s,
          expect ν (fun ω => X l (decode ω) * X k (decode ω) *
            X j (decode ω) * X i (decode ω))) ≤
      ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, ∑ l ∈ s,
          (expect ρ (fun ψ => X l ψ * X k ψ * X j ψ * X i ψ) + 2*ε) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro k hk
    apply Finset.sum_le_sum
    intro l hl
    exact hterm i hi j hj k hk l hl
  convert hsum using 1
  simp only [Finset.sum_add_distrib, Finset.sum_const_zero,
    Finset.sum_const, nsmul_eq_mul]
  ring

def centeredPair {Ψ : Type*} (Z : I → Ψ → Bool) (p : I → ℝ)
    (i : I) (ψ : Ψ) : ℝ :=
  (if Z i ψ then 1 else 0) - p i

/-- Precisely the mixed identities supplied by four-wise independence after
the pair indicators have been formed. The single-indicator moments are
proved above, and the fourth-moment inequality is derived below. -/
structure PairCrossMoments {Ψ : Type*} [Fintype Ψ]
    (ρ : FiniteLaw Ψ) (X : I → Ψ → ℝ) : Prop where
  cross1 : ∀ (s : Finset I) (i : I), i ∉ s →
    expect ρ (fun ψ => sumCentered X s ψ * X i ψ) = 0
  cross31 : ∀ (s : Finset I) (i : I), i ∉ s →
    expect ρ (fun ψ => (sumCentered X s ψ)^3 * X i ψ) = 0
  cross13 : ∀ (s : Finset I) (i : I), i ∉ s →
    expect ρ (fun ψ => sumCentered X s ψ * (X i ψ)^3) = 0
  cross22 : ∀ (s : Finset I) (i : I), i ∉ s →
    expect ρ (fun ψ => (sumCentered X s ψ)^2 * (X i ψ)^2) =
      expect ρ (fun ψ => (sumCentered X s ψ)^2) *
        expect ρ (fun ψ => (X i ψ)^2)

/-- Exact finite product-law factorization for one scalar factor per
coordinate.  This will discharge the `PairCrossMoments` fields for a genuine
product law rather than leave them as opaque assumptions. -/
theorem expect_pi_prod {A : Type*} [Fintype A]
    (μ : I → FiniteLaw A) (g : I → A → ℝ) :
    expect (FiniteLaw.pi μ) (fun x => ∏ i, g i (x i)) =
      ∏ i, expect (μ i) (g i) := by
  classical
  unfold expect
  change (∑ x : I → A, (∏ i, (μ i).weight (x i)) *
      (∏ i, g i (x i))) =
    ∏ i, ∑ a, (μ i).weight a * g i a
  calc
    _ = ∑ x : I → A, ∏ i, (μ i).weight (x i) * g i (x i) := by
      apply Finset.sum_congr rfl
      intro x _
      simpa only using (Finset.prod_mul_distrib
        (s := Finset.univ) (f := fun i => (μ i).weight (x i))
        (g := fun i => g i (x i))).symm
    _ = _ := (Fintype.prod_sum (fun i a => (μ i).weight a * g i a)).symm

/-- An ordered list of factors on possibly repeated coordinates has a
factorized expectation under the actual independent finite product. -/
theorem expect_pi_indexed_prod {A J : Type*} [Fintype A]
    (μ : I → FiniteLaw A) (t : Finset J) (idx : J → I)
    (f : J → A → ℝ) :
    expect (FiniteLaw.pi μ)
      (fun x => ∏ j ∈ t, f j (x (idx j))) =
    ∏ i, expect (μ i)
      (fun a => ∏ j ∈ t, if idx j = i then f j a else 1) := by
  classical
  have hpoint (x : I → A) :
      (∏ j ∈ t, f j (x (idx j))) =
        ∏ i, ∏ j ∈ t, if idx j = i then f j (x i) else 1 := by
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro j hj
    simpa using (Finset.prod_ite_eq_of_mem' (Finset.univ : Finset I) (idx j)
      (fun i => f j (x i)) (Finset.mem_univ _))
  simp_rw [hpoint]
  exact expect_pi_prod μ (fun i a => ∏ j ∈ t, if idx j = i then f j a else 1)

/-- A centered factor that appears at a unique coordinate annihilates an
indexed product. Repeated occurrences of the other three factors are allowed. -/
theorem expect_pi_indexed_prod_zero_unique {A J : Type*} [Fintype A]
    (μ : I → FiniteLaw A) (t : Finset J) (idx : J → I)
    (f : J → A → ℝ) (u : J) (hu : u ∈ t)
    (hunique : ∀ j ∈ t, idx j = idx u → j = u)
    (hmean : expect (μ (idx u)) (f u) = 0) :
    expect (FiniteLaw.pi μ)
      (fun x => ∏ j ∈ t, f j (x (idx j))) = 0 := by
  classical
  rw [expect_pi_indexed_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (idx u))
  have hpoint (a : A) :
      (∏ j ∈ t, if idx j = idx u then f j a else 1) = f u a := by
    rw [Finset.prod_eq_single_of_mem u hu]
    · simp
    · intro j hj hne
      have hidx : idx j ≠ idx u := fun h => hne (hunique j hj h)
      simp [hidx]
  simp only [hpoint, hmean]

/-- Equality of all finite event probabilities transports every real-valued
test function. This is the reusable bridge from `IsDWise` event marginals to
each quartic term on at most eight original coordinates. -/
theorem expect_eq_of_prob_preimage {Ψ : Type*} [Fintype Ψ]
    (ν : FiniteLaw Ω) (ρ : FiniteLaw Ψ) (decode : Ω → Ψ)
    (hprob : ∀ E : Ψ → Prop,
      ν.prob (fun ω => E (decode ω)) = ρ.prob E)
    (f : Ψ → ℝ) :
    expect ν (fun ω => f (decode ω)) = expect ρ f := by
  classical
  have hfibre (ψ : Ψ) :
      ν.prob (fun ω => decode ω = ψ) = ρ.weight ψ := by
    simpa only [FiniteLaw.prob_singleton] using hprob (fun x => x = ψ)
  calc
    expect ν (fun ω => f (decode ω)) =
        ∑ ψ, ν.prob (fun ω => decode ω = ψ) * f ψ := by
      unfold expect
      calc
        (∑ ω, ν.weight ω * f (decode ω)) =
            ∑ ω, ∑ ψ, if decode ω = ψ then ν.weight ω * f ψ else 0 := by
          apply Finset.sum_congr rfl
          intro ω _
          simp
        _ = ∑ ψ, ∑ ω, if decode ω = ψ then ν.weight ω * f ψ else 0 :=
          Finset.sum_comm
        _ = ∑ ψ, ν.prob (fun ω => decode ω = ψ) * f ψ := by
          apply Finset.sum_congr rfl
          intro ψ _
          rw [FiniteLaw.prob, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro ω _
          by_cases h : decode ω = ψ <;> simp [h]
    _ = expect ρ f := by simp only [hfibre, expect]

/-- Conditional pair-tail bound from exact product-law cross moments and
the `m⁴` good-marginal comparisons.  `K` is still an event of actual source
indices; `decode` never identifies equal labels on the source side. -/
theorem conditional_pair_tail
    {Ψ : Type*} [Fintype Ψ] {m : ℕ}
    (ν : FiniteLaw Ω) (ρ : FiniteLaw Ψ) (decode : Ω → Ψ)
    (Y K : Ω → Prop) [DecidablePred Y] (hY : 0 < ν.prob Y)
    (Z : Fin m → Ψ → Bool) (p : Fin m → ℝ) (ε : ℝ)
    (hm : 0 < m)
    (hp : ∀ i, p i = ρ.prob (fun ψ => Z i ψ))
    (hpSmall : ∀ i, p i < 9/25)
    (hK : ∀ ω, K ω → Y ω ∧ ∀ i, Z i (decode ω) = true)
    (hcross : PairCrossMoments ρ (centeredPair Z p))
    (hterm : ∀ i j k l : Fin m,
      expect (conditional ν Y hY) (fun ω =>
        centeredPair Z p l (decode ω) * centeredPair Z p k (decode ω) *
        centeredPair Z p j (decode ω) * centeredPair Z p i (decode ω)) ≤
      expect ρ (fun ψ => centeredPair Z p l ψ * centeredPair Z p k ψ *
        centeredPair Z p j ψ * centeredPair Z p i ψ) + 2*ε) :
    ν.prob K / ν.prob Y ≤
      (((m : ℝ)/4 + 3*(m : ℝ)^2/16) / ((16/25 : ℝ)^4 * (m : ℝ)^4)) +
        2*ε/(16/25 : ℝ)^4 := by
  classical
  let X := centeredPair Z p
  let S (ψ : Ψ) := ∑ i : Fin m, X i ψ
  let a : ℝ := (16/25 : ℝ) * m
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have ha : 0 < a := mul_pos (by norm_num) hmR
  have hsingle2 (i : Fin m) : expect ρ (fun ψ => (X i ψ)^2) ≤ 1/4 := by
    simpa only [X, centeredPair, ← hp i] using
      centered_indicator_second_le_quarter ρ (fun ψ => Z i ψ = true)
  have hsingle4 (i : Fin m) : expect ρ (fun ψ => (X i ψ)^4) ≤ 1/4 := by
    simpa only [X, centeredPair, ← hp i] using
      centered_indicator_fourth_le_quarter ρ (fun ψ => Z i ψ = true)
  have hprod := fourth_bound_of_cross_moments ρ X hsingle2 hsingle4
    hcross.cross1 hcross.cross31 hcross.cross13 hcross.cross22 Finset.univ
  have hprod4 : expect ρ (fun ψ => (S ψ)^4) ≤
      (m : ℝ)/4 + 3*(m : ℝ)^2/16 := by
    simpa only [S, sumCentered, Finset.sum_attach, Finset.card_univ,
      Fintype.card_fin] using hprod.2
  have hsource (ω : Ω) (hω : K ω) : a ≤ S (decode ω) := by
    have hpoints : ∀ i : Fin m, (16/25 : ℝ) ≤ X i (decode ω) := by
      intro i
      have hz := (hK ω hω).2 i
      have hp' := hpSmall i
      simp only [X, centeredPair, hz, ↓reduceIte]
      linarith
    calc
      a = ∑ _i : Fin m, (16/25 : ℝ) := by simp [a, mul_comm]
      _ ≤ ∑ i : Fin m, X i (decode ω) :=
        Finset.sum_le_sum (fun i _ => hpoints i)
  have hcondK := conditional_prob ν Y K hY (fun ω hω => (hK ω hω).1)
  have hmarkov := event_le_fourth_moment (conditional ν Y hY)
    (fun ω => S (decode ω)) K a ha hsource
  rw [hcondK] at hmarkov
  have hdiff := fourth_difference_of_terms (conditional ν Y hY) ρ decode X
    Finset.univ ε (by
      intro i _ j _ k _ l _
      exact hterm i j k l)
  have hcond4 : expect (conditional ν Y hY) (fun ω => (S (decode ω))^4) ≤
      (m : ℝ)/4 + 3*(m : ℝ)^2/16 + 2*ε*(m : ℝ)^4 := by
    calc
      _ ≤ expect ρ (fun ψ => (S ψ)^4) + 2*ε*(m : ℝ)^4 := by
        simpa only [S, Finset.card_univ, Fintype.card_fin] using hdiff
      _ ≤ (m : ℝ)/4 + 3*(m : ℝ)^2/16 + 2*ε*(m : ℝ)^4 :=
        by simpa only [add_comm] using
          (add_le_add_right hprod4 (2*ε*(m : ℝ)^4))
  have hbound := hmarkov.trans hcond4
  have hden : (0 : ℝ) < (16/25 : ℝ)^4 * (m : ℝ)^4 := by positivity
  have ha4 : a^4 = (16/25 : ℝ)^4 * (m : ℝ)^4 := by simp [a, mul_pow]
  rw [ha4] at hbound
  have hquot : ν.prob K / ν.prob Y ≤
      ((m : ℝ)/4 + 3*(m : ℝ)^2/16 + 2*ε*(m : ℝ)^4) /
        ((16/25 : ℝ)^4 * (m : ℝ)^4) := by
    apply (le_div_iff₀ hden).2
    simpa only [mul_comm] using hbound
  calc
    _ ≤ _ := hquot
    _ = ((m : ℝ)/4 + 3*(m : ℝ)^2/16) /
          ((16/25 : ℝ)^4 * (m : ℝ)^4) + 2*ε/(16/25 : ℝ)^4 := by
      field_simp

/-- The moderate-size part of Appendix H's pair argument. Combining this
with `conditional_pair_tail` yields the strict contradiction to retained
conditional mass at least `1/(4m)`. -/
theorem conditional_pair_numeric (m ε : ℝ) (hm : 16 ≤ m) (hε : 0 < ε)
    (hcap : m ≤ 1/(128*ε)) :
    (m/4 + 3*m^2/16) / ((16/25 : ℝ)^4 * m^4) +
      2*ε/(16/25 : ℝ)^4 < 1/(4*m) := by
  have hm0 : 0 < m := by linarith
  have hfirst := moderate_pair_numeric m hm
  have hcap' : 128*ε*m ≤ 1 := by
    have hden : 0 < 128*ε := by positivity
    have h := (le_div_iff₀ hden).mp hcap
    nlinarith
  have hα : (1/8 : ℝ) < (16/25 : ℝ)^4 := by norm_num
  have herr : 2*ε/(16/25 : ℝ)^4 < 1/(8*m) := by
    apply (div_lt_iff₀ (by positivity : 0 < (16/25 : ℝ)^4)).2
    have hcalc : 16*ε*m < (16/25 : ℝ)^4 := by linarith
    have hcalc' : (2*ε)*(8*m) < (16/25 : ℝ)^4 := by nlinarith
    have h := (lt_div_iff₀ (by positivity : 0 < 8*m)).2 hcalc'
    convert h using 1 <;> ring
  have hsum : 1/(8*m) + 1/(8*m) = (1 : ℝ)/(4*m) := by
    field_simp
    ring
  linarith

#print axioms fourth_bound_of_cross_moments
#print axioms event_le_fourth_moment
#print axioms exact_pair_numeric
#print axioms moderate_pair_numeric
#print axioms conditional_pair_tail
#print axioms conditional_pair_numeric

end CurrentAdditive.FourthMoment
