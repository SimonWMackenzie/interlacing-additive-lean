import Paper2.YaoSelectorEventsConcentration
import EthInapproximability.CurrentPaper.FinalPadding

/-!
# Unit 4 (Paper A), segment A4-S5: amplification, midpoint and error union

Owner lane `owner:a-unit4-shell` (private, 25 September 2026).
Source: lock v12 `01-introduction.tex`, proof of `intro:corollary` ("Choose a fixed
integer k>2a. Amplify the estimator's success probability to 99/100 by a constant
number of independent calls and a median. Accept the source exactly when its
estimate is below B+k/2."), and `intro:theorem` (NO probability `981/1000`).

Pure finite probability over Paper2's `FiniteLaw` (normalized nonnegative weights,
`iid` product law, `prod` independent pair law), reusing the banked Hoeffding bound
`FiniteLaw.iid_empirical_upper_tail` and two-stage accounting
`FiniteLaw.two_stage_failure_le`, and Paper B's banked integer midpoint lemmas
`FinalPadding.midpoint_yes` / `midpoint_no` by exact name.

The repetition count is the fixed constant `147` (odd). The median is the lower
median (smallest sample value `x` with a strict majority of samples `≤ x`).

**None of these statements closes a ledger row** (T01, T02, U18 stay open). No
estimator model, machine, tape layout or class definition is fixed here (D-A1, D-A3,
D-A4 are author decisions); every statement is generic in the estimate type/law.
-/

namespace Paper2.Unit4Shell.Amplification

open Paper2 Paper2.FiniteLaw

section Probability

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Complement rule for `FiniteLaw.prob`. Does not close a ledger row. -/
theorem prob_not (μ : FiniteLaw α) (E : α → Prop) :
    μ.prob (fun a => ¬ E a) = 1 - μ.prob E := by
  classical
  have h : μ.prob E + μ.prob (fun a => ¬ E a) = 1 := by
    unfold FiniteLaw.prob
    rw [← Finset.sum_add_distrib, ← μ.total]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hE : E a <;> simp [hE]
  linarith

/-- The fixed repetition count of the amplification. -/
def reps : ℕ := 147

theorem reps_odd : reps % 2 = 1 := by decide

open Classical in
/-- Hoeffding form: if one run fails with probability at most `1/3`, the probability
that at least half of `r` independent runs fail is at most `exp(-2 r / 49)`.
Does not close a ledger row. -/
theorem iid_half_bad_le_exp (μ : FiniteLaw α) (Bad : α → Prop)
    (hBad : μ.prob Bad ≤ 1 / 3) (r : ℕ) (hr : 0 < r) :
    (μ.iid r).prob (fun x => r ≤ 2 * Fintype.card {i : Fin r // Bad (x i)}) ≤
      Real.exp (-2 * r * (1 / 7 : ℝ) ^ 2) := by
  refine le_trans (FiniteLaw.prob_mono _ ?_) (μ.iid_empirical_upper_tail Bad r hr (1 / 7) (by norm_num))
  intro x hx
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hx' : (r : ℝ) ≤ 2 * (Fintype.card {i : Fin r // Bad (x i)} : ℝ) := by exact_mod_cast hx
  rw [lt_div_iff₀ hrR]
  nlinarith

/-- `exp(-6) ≤ 1/100`. -/
theorem exp_neg_six_le : Real.exp (-6) ≤ 1 / 100 := by
  have h1 := Real.exp_one_gt_d9
  have h6 : Real.exp 6 = Real.exp 1 ^ 6 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hpow : (2.7182818283 : ℝ) ^ 6 < Real.exp 1 ^ 6 :=
    pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have hbig : (100 : ℝ) ≤ Real.exp 6 := by
    rw [h6]; nlinarith [hpow]
  rw [Real.exp_neg]
  rw [inv_le_comm₀ (Real.exp_pos 6) (by norm_num)]
  simpa using hbig

open Classical in
/-- With `r = 147` runs, at least half fail with probability at most `1/100`.
Does not close a ledger row. -/
theorem iid_half_bad_le (μ : FiniteLaw α) (Bad : α → Prop)
    (hBad : μ.prob Bad ≤ 1 / 3) :
    (μ.iid reps).prob (fun x => reps ≤ 2 * Fintype.card {i : Fin reps // Bad (x i)}) ≤
      1 / 100 := by
  refine (iid_half_bad_le_exp μ Bad hBad reps (by decide)).trans ?_
  have : (-2 * (reps : ℝ) * (1 / 7 : ℝ) ^ 2) = -6 := by norm_num [reps]
  rw [this]
  exact exp_neg_six_le

open Classical in
/-- Strict-majority success: with per-run success probability at least `2/3`, a strict
majority of the `147` independent runs succeeds with probability at least `99/100`.
Does not close a ledger row. -/
theorem iid_majority_good_ge (μ : FiniteLaw α) (Good : α → Prop)
    (hGood : 2 / 3 ≤ μ.prob Good) :
    99 / 100 ≤ (μ.iid reps).prob
      (fun x => reps < 2 * Fintype.card {i : Fin reps // Good (x i)}) := by
  have hBad : μ.prob (fun a => ¬ Good a) ≤ 1 / 3 := by
    rw [prob_not]; linarith
  have h := iid_half_bad_le μ (fun a => ¬ Good a) hBad
  have hsub : ∀ x : Fin reps → α,
      ¬ (reps < 2 * Fintype.card {i : Fin reps // Good (x i)}) →
        reps ≤ 2 * Fintype.card {i : Fin reps // ¬ Good (x i)} := by
    intro x hx
    have hsum : Fintype.card {i : Fin reps // Good (x i)} +
        Fintype.card {i : Fin reps // ¬ Good (x i)} = reps := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin]
      have := Fintype.card_subtype_le (fun i : Fin reps => Good (x i))
      simp only [Fintype.card_fin] at this
      omega
    omega
  have hmono := FiniteLaw.prob_mono (μ.iid reps) hsub
  rw [prob_not] at hmono
  have h' : (μ.iid reps).prob
      (fun a => reps ≤ 2 * Fintype.card {i : Fin reps // ¬ Good (a i)}) ≤ 1 / 100 := by
    convert h
  linarith

/-- Two-stage error union: reduction tape `b` (law `ρ`) followed by `147` independent
estimator runs (law `μ`), with the per-run correctness allowed to depend on the reduction
output. On a good reduction tape a single run is correct with probability `≥ 2/3`. Then the
event "the reduction tape is good and a strict majority of runs is correct" fails with
probability at most `ε + 1/100`. Does not close a ledger row. -/
theorem two_stage_majority_failure_le (ρ : FiniteLaw β) (μ : FiniteLaw α)
    (GoodTape : β → Prop) (Correct : β → α → Prop) (ε : ℝ)
    (hρ : ρ.prob (fun b => ¬ GoodTape b) ≤ ε)
    (hμ : ∀ b, GoodTape b → 2 / 3 ≤ μ.prob (Correct b)) :
    (ρ.prod (μ.iid reps)).prob (fun x => ¬ (GoodTape x.1 ∧
      reps < 2 * (by classical exact Fintype.card {i : Fin reps // Correct x.1 (x.2 i)}))) ≤
      ε + 1 / 100 := by
  classical
  have h := FiniteLaw.two_stage_failure_le ρ (μ.iid reps) GoodTape
    (fun b xs => ¬ (GoodTape b ∧
      reps < 2 * Fintype.card {i : Fin reps // Correct b (xs i)}))
    ε (1 / 100) hρ ?_ (by norm_num)
  · convert h using 3
  · intro b hb
    have hg := iid_majority_good_ge μ (Correct b) (hμ b hb)
    have hc : (μ.iid reps).prob (fun xs => ¬ (GoodTape b ∧
        reps < 2 * Fintype.card {i : Fin reps // Correct b (xs i)})) =
        (μ.iid reps).prob (fun xs => ¬
          (reps < 2 * Fintype.card {i : Fin reps // Correct b (xs i)})) := by
      congr 1
      funext xs
      simp [hb]
    rw [hc, prob_not]
    linarith

/-- Numerical closure used by T01/T02: `(1/2)^11 + 1/100 < 1/3` and
`981/1000 ≤ 1 - (1/2)^11`. Does not close a ledger row. -/
theorem error_budget : ((1 / 2 : ℝ) ^ 11 + 1 / 100 < 1 / 3) ∧
    ((981 / 1000 : ℝ) ≤ 1 - (1 / 2 : ℝ) ^ 11) := by
  constructor <;> norm_num

end Probability

section Median

variable {β : Type*} [LinearOrder β]

/-- Lower median of `r ≥ 1` samples: the smallest sample value `x` such that a strict
majority of samples is `≤ x`. Does not close a ledger row. -/
noncomputable def lowerMedian {r : ℕ} (hr : 0 < r) (v : Fin r → β) : β := by
  classical
  exact ((Finset.univ.image v).filter
    (fun x => r < 2 * (Finset.univ.filter fun i => v i ≤ x).card)).min' (by
      let i0 : Fin r := ⟨0, hr⟩
      obtain ⟨m, hm, hmax⟩ := (Finset.univ.image v).exists_max_image id
        ⟨v i0, Finset.mem_image_of_mem v (Finset.mem_univ i0)⟩
      refine ⟨m, Finset.mem_filter.mpr ⟨hm, ?_⟩⟩
      have hall : (Finset.univ.filter fun i => v i ≤ m) = Finset.univ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact hmax (v i) (Finset.mem_image_of_mem v (Finset.mem_univ i))
      rw [hall, Finset.card_univ, Fintype.card_fin]
      omega)

theorem lowerMedian_spec {r : ℕ} (hr : 0 < r) (v : Fin r → β) :
    (∃ i, v i = lowerMedian hr v) ∧
    r < 2 * (Finset.univ.filter fun i => v i ≤ lowerMedian hr v).card ∧
    ∀ i, r < 2 * (Finset.univ.filter fun j => v j ≤ v i).card → lowerMedian hr v ≤ v i := by
  classical
  unfold lowerMedian
  set S := ((Finset.univ.image v).filter
    (fun x => r < 2 * (Finset.univ.filter fun i => v i ≤ x).card))
  have hne : S.Nonempty := by
    let i0 : Fin r := ⟨0, hr⟩
    obtain ⟨m, hm, hmax⟩ := (Finset.univ.image v).exists_max_image id
      ⟨v i0, Finset.mem_image_of_mem v (Finset.mem_univ i0)⟩
    refine ⟨m, Finset.mem_filter.mpr ⟨hm, ?_⟩⟩
    have hall : (Finset.univ.filter fun i => v i ≤ m) = Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact hmax (v i) (Finset.mem_image_of_mem v (Finset.mem_univ i))
    rw [hall, Finset.card_univ, Fintype.card_fin]
    omega
  have hmem := S.min'_mem hne
  have hmem' := Finset.mem_filter.mp hmem
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem'.1
    exact ⟨i, hi⟩
  · convert hmem'.2 using 3
  · intro i hi
    apply S.min'_le
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem v (Finset.mem_univ i), hi⟩

/-- Median below a threshold iff a strict majority of samples is below it.
Does not close a ledger row. -/
theorem lowerMedian_lt_iff {r : ℕ} (hr : 0 < r) (v : Fin r → β) (θ : β) :
    lowerMedian hr v < θ ↔ r < 2 * (Finset.univ.filter fun i => v i < θ).card := by
  classical
  obtain ⟨_, hmaj, hmin⟩ := lowerMedian_spec hr v
  constructor
  · intro hlt
    refine lt_of_lt_of_le hmaj (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact lt_of_le_of_lt hi hlt
  · intro hmaj'
    have hpos : (Finset.univ.filter fun i => v i < θ).Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨j, hj, hjmax⟩ := (Finset.univ.filter fun i => v i < θ).exists_max_image v hpos
    have hjθ : v j < θ := (Finset.mem_filter.mp hj).2
    have hsame : (Finset.univ.filter fun i => v i ≤ v j) =
        (Finset.univ.filter fun i => v i < θ) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact lt_of_le_of_lt h hjθ
      · intro h
        exact hjmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
    have hle := hmin j (by rw [hsame]; exact hmaj')
    exact lt_of_le_of_lt hle hjθ

/-- A strict majority of samples above a threshold forces the median above it.
Does not close a ledger row. -/
theorem lt_lowerMedian_of_majority {r : ℕ} (hr : 0 < r) (v : Fin r → β) (θ : β)
    (hmaj : r < 2 * (Finset.univ.filter fun i => θ < v i).card) :
    θ < lowerMedian hr v := by
  classical
  by_contra hle'
  have hle := not_lt.mp hle'
  obtain ⟨_, hmaj', _⟩ := lowerMedian_spec hr v
  have hdisj : (Finset.univ.filter fun i => v i ≤ lowerMedian hr v).card +
      (Finset.univ.filter fun i => θ < v i).card ≤ r := by
    rw [← Finset.card_union_of_disjoint]
    · calc _ ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_le_univ _
        _ = r := by simp
    · rw [Finset.disjoint_filter]
      intro i _ h1 h2
      exact absurd (lt_of_lt_of_le h2 (h1.trans hle)) (lt_irrefl _)
  omega

end Median

section Midpoint

/-- Midpoint separation, YES side, real estimate and real error `a` with `2a < k`.
Does not close a ledger row. -/
theorem midpoint_yes_real (e a : ℝ) (D B k : ℕ) (hD : D ≤ B)
    (herr : |e - D| ≤ a) (hk : 2 * a < k) : e < (B : ℝ) + (k : ℝ) / 2 := by
  have h := (abs_le.mp herr).2
  have hDB : (D : ℝ) ≤ B := by exact_mod_cast hD
  linarith

/-- Midpoint separation, NO side (`D = B + k`). Does not close a ledger row. -/
theorem midpoint_no_real (e a : ℝ) (B k : ℕ)
    (herr : |e - ((B + k : ℕ) : ℝ)| ≤ a) (hk : 2 * a < k) : (B : ℝ) + (k : ℝ) / 2 < e := by
  have h := (abs_le.mp herr).1
  push_cast at h
  linarith

/-- Signed-integer form with a real error bound `a`, `2a < k`: reduces to the banked
integer lemmas `FinalPadding.midpoint_yes`/`midpoint_no` with `A = ⌊a⌋₊`.
Does not close a ledger row. -/
theorem midpoint_int_of_real (z : ℤ) (a : ℝ) (ha : 0 ≤ a) (D B k : ℕ)
    (herr : |(z : ℝ) - D| ≤ a) (hk : 2 * a < k) :
    (D ≤ B → 2 * z < 2 * (B : ℤ) + (k : ℤ)) ∧
    (D = B + k → 2 * (B : ℤ) + (k : ℤ) < 2 * z) := by
  have hA : |z - (D : ℤ)| ≤ ((⌊a⌋₊ : ℕ) : ℤ) := by
    have h1 : ((|z - (D : ℤ)| : ℤ) : ℝ) ≤ a := by push_cast; exact herr
    have h2 : |z - (D : ℤ)| = ((Int.toNat |z - (D : ℤ)| : ℕ) : ℤ) :=
      (Int.toNat_of_nonneg (abs_nonneg _)).symm
    rw [h2] at h1 ⊢
    have h3 : ((Int.toNat |z - (D : ℤ)| : ℕ) : ℝ) ≤ a := by exact_mod_cast h1
    exact_mod_cast Nat.le_floor h3
  have hgap : 2 * ⌊a⌋₊ < k := by
    have := Nat.floor_le ha
    have hk' : (2 * ⌊a⌋₊ : ℝ) < k := by linarith
    exact_mod_cast hk'
  refine ⟨fun hD => EthInapproximability.CurrentPaper.FinalPadding.midpoint_yes
    z D B ⌊a⌋₊ k hD hA hgap, fun hD => ?_⟩
  subst hD
  exact EthInapproximability.CurrentPaper.FinalPadding.midpoint_no z B ⌊a⌋₊ k
    (by simpa using hA) hgap

/-- Dyadic comparison with the midpoint as one integer comparison:
`z / 2^j < B + k/2 ↔ 2z < 2^j (2B + k)`. Does not close a ledger row. -/
theorem dyadic_lt_midpoint_iff (z : ℤ) (j B k : ℕ) :
    ((z : ℚ) / 2 ^ j < (B : ℚ) + (k : ℚ) / 2) ↔ 2 * z < 2 ^ j * (2 * (B : ℤ) + k) := by
  have hpos : (0 : ℚ) < 2 ^ j := by positivity
  rw [div_lt_iff₀ hpos]
  constructor
  · intro h
    have : ((2 * z : ℤ) : ℚ) < ((2 ^ j * (2 * (B : ℤ) + k) : ℤ) : ℚ) := by
      push_cast; nlinarith
    exact_mod_cast this
  · intro h
    have : ((2 * z : ℤ) : ℚ) < ((2 ^ j * (2 * (B : ℤ) + k) : ℤ) : ℚ) := by exact_mod_cast h
    push_cast at this
    nlinarith

/-- Rounding lemma: flooring a rational estimate keeps an integer additive error bound
around an integer target. Does not close a ledger row. -/
theorem floor_error (e : ℚ) (D A : ℤ) (herr : |e - D| ≤ A) : |⌊e⌋ - D| ≤ A := by
  have h := abs_le.mp herr
  rw [abs_le]
  constructor
  · have : ((D - A : ℤ) : ℚ) ≤ e := by push_cast; linarith
    have := Int.le_floor.mpr this
    omega
  · have h1 : ((⌊e⌋ : ℤ) : ℚ) ≤ e := Int.floor_le e
    have : ((⌊e⌋ : ℤ) : ℚ) ≤ ((D + A : ℤ) : ℚ) := by push_cast; linarith
    have := (Int.cast_le (R := ℚ)).mp this
    omega

end Midpoint

section MedianMidpoint

open Classical in
/-- Median-of-runs midpoint test, YES side: if a strict majority of the `r` estimates is
within `a` of the cost `D ≤ B` (and `2a < k`), the median lies below `B + k/2`.
Does not close a ledger row. -/
theorem median_midpoint_yes {r : ℕ} (hr : 0 < r) (v : Fin r → ℝ) (a : ℝ) (D B k : ℕ)
    (hD : D ≤ B) (hk : 2 * a < k)
    (hmaj : r < 2 * Fintype.card {i : Fin r // |v i - D| ≤ a}) :
    lowerMedian hr v < (B : ℝ) + (k : ℝ) / 2 := by
  rw [lowerMedian_lt_iff]
  rw [Fintype.card_subtype] at hmaj
  refine lt_of_lt_of_le hmaj (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact midpoint_yes_real _ _ _ _ _ hD hi hk

open Classical in
/-- Median-of-runs midpoint test, NO side (`D = B + k`). Does not close a ledger row. -/
theorem median_midpoint_no {r : ℕ} (hr : 0 < r) (v : Fin r → ℝ) (a : ℝ) (B k : ℕ)
    (hk : 2 * a < k)
    (hmaj : r < 2 * Fintype.card {i : Fin r // |v i - ((B + k : ℕ) : ℝ)| ≤ a}) :
    (B : ℝ) + (k : ℝ) / 2 < lowerMedian hr v := by
  apply lt_lowerMedian_of_majority
  rw [Fintype.card_subtype] at hmaj
  refine lt_of_lt_of_le hmaj (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact midpoint_no_real _ _ _ _ hi hk

end MedianMidpoint

end Paper2.Unit4Shell.Amplification
