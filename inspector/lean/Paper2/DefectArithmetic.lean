import Mathlib

/-!
# Exact arithmetic for the column-defect induction

Frozen Paper 2 v12, Appendix A, `cl:defect-induction`,
`cl:ceiling-halving`, `cl:half-defect`, and `cl:alice-allocation`.
The cutoff uses integer powers in the real numbers: at level zero it is
one half, not the natural-number value obtained by truncating `a-1`.
These statements prove the arithmetic; they do not assume an induction
state, a selected protocol branch, or a communication lower bound.
-/

namespace Paper2.DefectArithmetic

/-- The source's real cutoff `2^(a-1)`, including `a=0`. -/
noncomputable def cutoff (a : ℕ) : ℝ := (2 : ℝ) ^ ((a : ℤ) - 1)

@[simp] theorem cutoff_zero : cutoff 0 = 1 / 2 := by norm_num [cutoff]
@[simp] theorem cutoff_one : cutoff 1 = 1 := by norm_num [cutoff]
@[simp] theorem cutoff_two : cutoff 2 = 2 := by norm_num [cutoff]

theorem cutoff_pos (a : ℕ) : 0 < cutoff a := by
  exact zpow_pos (by norm_num) _

theorem cutoff_succ (a : ℕ) : cutoff (a + 1) = 2 * cutoff a := by
  unfold cutoff
  have he : (((a + 1 : ℕ) : ℤ) - 1) = ((a : ℤ) - 1) + 1 := by omega
  rw [he, zpow_add₀ (by norm_num)]
  simp
  ring

theorem cutoff_pred (a : ℕ) (ha : 1 ≤ a) : cutoff a = 2 * cutoff (a - 1) := by
  have he : a = (a - 1) + 1 := by omega
  conv_lhs => rw [he]
  exact cutoff_succ (a - 1)

theorem cutoff_nat (a : ℕ) (ha : 1 ≤ a) : cutoff a = (2 : ℝ) ^ (a - 1) := by
  unfold cutoff
  rw [show (a : ℤ) - 1 = ((a - 1 : ℕ) : ℤ) by omega, zpow_natCast]

theorem cutoff_eq_pow_div_two (a : ℕ) : cutoff a = (2 : ℝ) ^ a / 2 := by
  induction a with
  | zero => norm_num
  | succ a ih => rw [cutoff_succ, ih, pow_succ]; ring

theorem cutoff_mono {a b : ℕ} (hab : a ≤ b) : cutoff a ≤ cutoff b := by
  rw [cutoff_eq_pow_div_two, cutoff_eq_pow_div_two]
  exact div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hab) (by norm_num)

theorem cutoff_lt_iff_pow_lt (a p : ℕ) : cutoff a < (p : ℝ) ↔ 2 ^ a < 2 * p := by
  rw [cutoff_eq_pow_div_two, div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
  norm_cast
  omega

/-- The exact integer row floor from the manuscript. -/
noncomputable def rowThreshold (m a : ℕ) (theta : ℝ) : ℕ :=
  ⌈(m : ℝ) * (2 : ℝ) ^ a * theta⌉₊

theorem rowThreshold_halving (m a : ℕ) (theta : ℝ) (ha : 1 ≤ a) :
    rowThreshold m (a - 1) theta ≤ ⌈(rowThreshold m a theta : ℝ) / 2⌉₊ := by
  unfold rowThreshold
  apply Nat.ceil_le_ceil
  have he : a = (a - 1) + 1 := by omega
  have hp : (m : ℝ) * (2 : ℝ) ^ (a - 1) * theta =
      ((m : ℝ) * (2 : ℝ) ^ a * theta) / 2 := by
    conv_rhs => rw [he, pow_succ]
    ring
  rw [hp]
  exact div_le_div_of_nonneg_right (Nat.le_ceil _) (by norm_num)

theorem rowThreshold_mono (m : ℕ) {a b : ℕ} {theta : ℝ}
    (htheta : 0 ≤ theta) (hab : a ≤ b) :
    rowThreshold m a theta ≤ rowThreshold m b theta := by
  unfold rowThreshold
  apply Nat.ceil_le_ceil
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hab) (by positivity)) htheta

/-- The extra one-bit defect allowance. At zero it is totalized, but all
comparisons involving a reciprocal require a positive denominator. -/
noncomputable def envelope (p : ℕ) : ℝ := 1 + 1 / (p : ℝ)

theorem envelope_nonneg (p : ℕ) : 0 ≤ envelope p := by unfold envelope; positivity

theorem envelope_antitone {p q : ℕ} (hq : 0 < q) (hqp : q ≤ p) :
    envelope p ≤ envelope q := by
  unfold envelope
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqpR : (q : ℝ) ≤ p := by exact_mod_cast hqp
  exact add_le_add_right (one_div_le_one_div_of_le hqR hqpR) 1

theorem envelope_le_two {p : ℕ} (hp : 0 < p) : envelope p ≤ 2 := by
  have h := envelope_antitone (p := p) (q := 1) (by decide) (by omega)
  norm_num [envelope] at h ⊢
  exact h

theorem envelope_le_pair {p p₀ p₁ : ℕ} (hp : 0 < p) :
    envelope p ≤ envelope p₀ + envelope p₁ := by
  have h0 : 0 ≤ 1 / (p₀ : ℝ) := by positivity
  have h1 : 0 ≤ 1 / (p₁ : ℝ) := by positivity
  have h := envelope_le_two hp
  unfold envelope at *
  linarith

/-- The source's surplus inequality, before any eligibility choice. -/
theorem surplus_sum (u v h : ℝ) :
    u + v - 2 * h ≤ max (u - h) 0 + max (v - h) 0 := by
  have h0 := le_max_left (u - h) 0
  have h1 := le_max_left (v - h) 0
  linarith

/-- Alice's allocation rule, including sole-eligible and both-eligible
cases. The allowance flag can be any nonnegative real, so both source
values `e=0,1` are included without a separate assumed selection rule. -/
theorem alice_allocation (p p₀ p₁ : ℕ) (h delta e L₀ L₁ : ℝ)
    (hsum : p₀ + p₁ = p) (hh : 0 ≤ h) (hp : 2 * h < p)
    (hdelta : 0 ≤ delta) (he : 0 ≤ e) (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁)
    (hbudget : L₀ + L₁ ≤ ((p : ℝ) - 2 * h) * delta + e * envelope p) :
    (h < p₀ ∧ L₀ ≤ ((p₀ : ℝ) - h) * delta + e * envelope p₀) ∨
    (h < p₁ ∧ L₁ ≤ ((p₁ : ℝ) - h) * delta + e * envelope p₁) := by
  have hsumR : (p₀ : ℝ) + p₁ = p := by exact_mod_cast hsum
  have hpN : 0 < p := by exact_mod_cast (by linarith : (0 : ℝ) < p)
  by_cases h0 : h < (p₀ : ℝ)
  · have hp0 : 0 < p₀ := by exact_mod_cast (lt_of_le_of_lt hh h0)
    by_cases h1 : h < (p₁ : ℝ)
    · by_contra hn
      have hL0 : ((p₀ : ℝ) - h) * delta + e * envelope p₀ < L₀ := by
        by_contra hle
        exact hn (Or.inl ⟨h0, le_of_not_gt hle⟩)
      have hL1 : ((p₁ : ℝ) - h) * delta + e * envelope p₁ < L₁ := by
        by_contra hle
        exact hn (Or.inr ⟨h1, le_of_not_gt hle⟩)
      have henv := mul_le_mul_of_nonneg_left
        (envelope_le_pair (p₀ := p₀) (p₁ := p₁) hpN) he
      nlinarith
    · left
      refine ⟨h0, ?_⟩
      have hsur : ((p : ℝ) - 2 * h) * delta ≤ ((p₀ : ℝ) - h) * delta :=
        mul_le_mul_of_nonneg_right (by linarith) hdelta
      have henv := mul_le_mul_of_nonneg_left
        (envelope_antitone hp0 (by omega : p₀ ≤ p)) he
      linarith
  · have h1 : h < (p₁ : ℝ) := by linarith
    have hp1 : 0 < p₁ := by exact_mod_cast (lt_of_le_of_lt hh h1)
    right
    refine ⟨h1, ?_⟩
    have hsur : ((p : ℝ) - 2 * h) * delta ≤ ((p₁ : ℝ) - h) * delta :=
      mul_le_mul_of_nonneg_right (by linarith) hdelta
    have henv := mul_le_mul_of_nonneg_left
      (envelope_antitone hp1 (by omega : p₁ ≤ p)) he
    linarith

def ceilHalf (p : ℕ) : ℕ := (p + 1) / 2

theorem ceilHalf_bounds (p : ℕ) :
    p ≤ 2 * ceilHalf p ∧ 2 * ceilHalf p ≤ p + 1 ∧ ceilHalf p ≤ p := by
  unfold ceilHalf
  omega

theorem ceilHalf_pos {p : ℕ} (hp : 0 < p) : 0 < ceilHalf p := by
  have h := ceilHalf_bounds p
  omega

theorem ceilHalf_eq_ceil (p : ℕ) : ceilHalf p = ⌈(p : ℝ) / 2⌉₊ := by
  apply le_antisymm
  · have hc := Nat.le_ceil ((p : ℝ) / 2)
    have hr : (p : ℝ) ≤ 2 * (⌈(p : ℝ) / 2⌉₊ : ℝ) := by linarith
    have hn : p ≤ 2 * ⌈(p : ℝ) / 2⌉₊ := by exact_mod_cast hr
    unfold ceilHalf
    omega
  · apply Nat.ceil_le.mpr
    have hr : (p : ℝ) ≤ 2 * (ceilHalf p : ℝ) := by
      exact_mod_cast (ceilHalf_bounds p).1
    linarith

theorem rowThreshold_halving_integer (m a : ℕ) (theta : ℝ) (ha : 1 ≤ a) :
    rowThreshold m (a - 1) theta ≤ ceilHalf (rowThreshold m a theta) := by
  rw [ceilHalf_eq_ceil]
  exact rowThreshold_halving m a theta ha

/-- The surplus component of Bob's half-defect calculation. -/
theorem half_surplus (p : ℕ) (h : ℝ) (hp : 0 < p) (hh : 0 ≤ h) :
    ((ceilHalf p : ℝ) / p) * ((p : ℝ) - 2 * h) ≤ (ceilHalf p : ℝ) - h := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (p : ℝ) ≤ 2 * (ceilHalf p : ℝ) := by
    exact_mod_cast (ceilHalf_bounds p).1
  have he : (((ceilHalf p : ℝ) / p) * ((p : ℝ) - 2 * h)) =
      ((ceilHalf p : ℝ) * ((p : ℝ) - 2 * h)) / p := by ring
  rw [he]
  apply (div_le_iff₀ hpR).mpr
  nlinarith

/-- The exact additional-defect inequality uses `p>=5`; unlike a looser
envelope it is not silently extended to the smaller odd endpoint. -/
theorem half_envelope (p : ℕ) (hp : 5 ≤ p) :
    ((ceilHalf p : ℝ) / p) * (2 + 1 / (p : ℝ)) ≤ envelope (ceilHalf p) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hqN : 3 ≤ ceilHalf p := by have h := ceilHalf_bounds p; omega
  have hqR : (3 : ℝ) ≤ ceilHalf p := by exact_mod_cast hqN
  have hqpos : (0 : ℝ) < ceilHalf p := by linarith
  have hl : ((ceilHalf p : ℝ) / p) * (2 + 1 / (p : ℝ)) =
      ((ceilHalf p : ℝ) * (2 * (p : ℝ) + 1)) / (p : ℝ) ^ 2 := by
    field_simp
  have hr : envelope (ceilHalf p) = ((ceilHalf p : ℝ) + 1) / (ceilHalf p : ℝ) := by
    unfold envelope
    field_simp
  rw [hl, hr]
  apply (div_le_div_iff₀ (sq_pos_of_pos hpR) hqpos).mpr
  have hparity : p = 2 * ceilHalf p ∨ p + 1 = 2 * ceilHalf p := by
    unfold ceilHalf
    omega
  rcases hparity with heven | hodd
  · have he : (p : ℝ) = 2 * (ceilHalf p : ℝ) := by exact_mod_cast heven
    rw [he]
    nlinarith [sq_nonneg (ceilHalf p : ℝ)]
  · have ho : (p : ℝ) = 2 * (ceilHalf p : ℝ) - 1 := by
      have hc : (p : ℝ) + 1 = 2 * (ceilHalf p : ℝ) := by exact_mod_cast hodd
      linarith
    rw [ho]
    have hfact : 0 ≤ (ceilHalf p : ℝ) * ((ceilHalf p : ℝ) - 3) :=
      mul_nonneg hqpos.le (by linarith)
    nlinarith

/-- Averaging after a Bob bit takes the `e=1` allowance to the next
smaller level, with the exact source envelope. -/
theorem bob_half_allowance (a p : ℕ) (delta : ℝ) (ha : 1 ≤ a)
    (hp : 5 ≤ p) (hdelta : 0 ≤ delta) :
    ((ceilHalf p : ℝ) / p) *
        (((p : ℝ) - cutoff a) * delta + envelope p + 1) ≤
      ((ceilHalf p : ℝ) - cutoff (a - 1)) * delta + envelope (ceilHalf p) := by
  rw [cutoff_pred a ha]
  have hs := mul_le_mul_of_nonneg_right
    (half_surplus p (cutoff (a - 1)) (by omega) (cutoff_pos _).le) hdelta
  have he := half_envelope p hp
  unfold envelope at *
  nlinarith

theorem half_eligible (a p : ℕ) (ha : 1 ≤ a) (hp : cutoff a < (p : ℝ)) :
    cutoff (a - 1) < (ceilHalf p : ℝ) := by
  rw [cutoff_pred a ha] at hp
  have h : (p : ℝ) ≤ 2 * (ceilHalf p : ℝ) := by
    exact_mod_cast (ceilHalf_bounds p).1
  linarith

/-- One-coordinate projection in the `(0,0)` base has strictly less
defect than `delta`, including the real half cutoff. -/
theorem base_zero_projection (p : ℕ) (delta : ℝ) (hp : 0 < p) (hdelta : 0 < delta) :
    (1 / (p : ℝ)) * (((p : ℝ) - cutoff 0) * delta) < delta := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [cutoff_zero]
  have he : (1 / (p : ℝ)) * (((p : ℝ) - 1/2) * delta) =
      (((p : ℝ) - 1/2) * delta) / p := by ring
  rw [he]
  apply (div_lt_iff₀ hpR).mpr
  nlinarith

theorem three_envelope (p : ℕ) (hp : 3 ≤ p) :
    (3 / (p : ℝ)) * envelope p ≤ 4 / 3 := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  unfold envelope
  have he : (3 / (p : ℝ)) * (1 + 1 / (p : ℝ)) =
      (3 * (p : ℝ) + 3) / (p : ℝ) ^ 2 := by field_simp
  rw [he]
  apply (div_le_iff₀ (sq_pos_of_pos hp0)).mpr
  have hfact : 0 ≤ ((p : ℝ) - 3) * (4 * (p : ℝ) + 3) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem base_three_projection (p : ℕ) (delta : ℝ) (hp : 3 ≤ p) (hdelta : 0 ≤ delta) :
    (3 / (p : ℝ)) * (((p : ℝ) - 2) * delta + envelope p) ≤ 3 * delta + 4 / 3 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hs : (3 / (p : ℝ)) * (((p : ℝ) - 2) * delta) ≤ 3 * delta := by
    have he : (3 / (p : ℝ)) * (((p : ℝ) - 2) * delta) =
        (3 * ((p : ℝ) - 2) * delta) / p := by ring
    rw [he]
    apply (div_le_iff₀ hp0).mpr
    nlinarith
  have he := three_envelope p hp
  linarith

theorem base_two_projection (p : ℕ) (delta : ℝ) (hp : 2 ≤ p) (hdelta : 0 ≤ delta) :
    (2 / (p : ℝ)) * (((p : ℝ) - 1) * delta + 1) ≤ 2 * delta + 1 := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have he : (2 / (p : ℝ)) * (((p : ℝ) - 1) * delta + 1) =
      (2 * (((p : ℝ) - 1) * delta + 1)) / p := by ring
  rw [he]
  apply (div_le_iff₀ hp0).mpr
  nlinarith

/-- All non-base induction transitions strictly decrease the source's
integer induction rank. -/
theorem alice_rank_decreases (a e : ℕ) (ha : 1 ≤ a) (he : e ≤ 1) :
    2 * (a - 1) + 1 - e < 2 * a + 1 - e := by omega

theorem bob_zero_rank_decreases (a : ℕ) :
    2 * a + 1 - 1 < 2 * a + 1 := by omega

theorem bob_one_rank_decreases (a : ℕ) (ha : 1 ≤ a) :
    2 * (a - 1) + 1 - 1 < 2 * a + 1 - 1 := by omega

theorem alice_child_flag_admissible (a e : ℕ) (he : e ≤ 1) (ha : 2 * e ≤ a)
    (ha1 : 1 ≤ a) (hbase : ¬ (a = 2 ∧ e = 1)) : 2 * e ≤ a - 1 := by omega

/-- Alice's rule directly in the source's level and flag parameters. -/
theorem alice_level_allocation (a p p₀ p₁ e : ℕ) (delta L₀ L₁ : ℝ)
    (ha : 1 ≤ a) (hsum : p₀ + p₁ = p) (hp : cutoff a < (p : ℝ))
    (hdelta : 0 ≤ delta) (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁)
    (hbudget : L₀ + L₁ ≤ ((p : ℝ) - cutoff a) * delta + (e : ℝ) * envelope p) :
    (cutoff (a - 1) < p₀ ∧
      L₀ ≤ ((p₀ : ℝ) - cutoff (a - 1)) * delta + (e : ℝ) * envelope p₀) ∨
    (cutoff (a - 1) < p₁ ∧
      L₁ ≤ ((p₁ : ℝ) - cutoff (a - 1)) * delta + (e : ℝ) * envelope p₁) := by
  rw [cutoff_pred a ha] at hp hbudget
  exact alice_allocation p p₀ p₁ (cutoff (a - 1)) delta (e : ℝ) L₀ L₁
    hsum (cutoff_pos _).le hp hdelta (by positivity) hL₀ hL₁ hbudget

/-- An `e=0` Bob child can be charged to flag one without projection. -/
theorem bob_zero_allowance (p a : ℕ) (delta : ℝ) :
    ((p : ℝ) - cutoff a) * delta + 1 ≤
      ((p : ℝ) - cutoff a) * delta + envelope p := by
  unfold envelope
  have h : 0 ≤ 1 / (p : ℝ) := by positivity
  linarith

theorem eligible_ge_three (a p : ℕ) (ha : 2 ≤ a) (hp : cutoff a < (p : ℝ)) :
    3 ≤ p := by
  have h := cutoff_mono ha
  rw [cutoff_two] at h
  have hlt : (2 : ℝ) < p := lt_of_le_of_lt h hp
  exact_mod_cast hlt

theorem eligible_ge_five (a p : ℕ) (ha : 3 ≤ a) (hp : cutoff a < (p : ℝ)) :
    5 ≤ p := by
  have h := cutoff_mono ha
  have hthree : cutoff 3 = 4 := by norm_num [cutoff]
  rw [hthree] at h
  have hlt : (4 : ℝ) < p := lt_of_le_of_lt h hp
  exact_mod_cast hlt

/-- Every remaining state fits the three-coordinate nonconstancy base. -/
theorem state_le_three_base (a p e : ℕ) (delta : ℝ)
    (ha : 2 ≤ a) (he : e ≤ 1) (hdelta : 0 ≤ delta) :
    ((p : ℝ) - cutoff a) * delta + (e : ℝ) * envelope p ≤
      ((p : ℝ) - 2) * delta + envelope p := by
  have hc := cutoff_mono ha
  rw [cutoff_two] at hc
  have hs := mul_le_mul_of_nonneg_right (sub_le_sub_left hc (p : ℝ)) hdelta
  have hflag : (e : ℝ) ≤ 1 := by exact_mod_cast he
  have hb := mul_le_mul_of_nonneg_right hflag (envelope_nonneg p)
  linarith

theorem two_base_strict_margin (delta : ℝ) (hdelta : 0 ≤ delta) :
    2 * delta + 1 < 3 * delta + 4 / 3 := by linarith

/-- Once `a>=1`, passing to level `a-1` retains the scale guard. -/
theorem pred_scale_guard (a : ℕ) (theta : ℝ)
    (htheta : 0 ≤ theta) (hscale : (2 : ℝ) ^ a * theta ≤ 1) :
    (2 : ℝ) ^ (a - 1) * theta ≤ 1 := by
  exact (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) (Nat.sub_le a 1)) htheta).trans hscale

end Paper2.DefectArithmetic
