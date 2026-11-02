import Mathlib

/-!
# Dyadic support floors and integer capacities

Frozen v12 Section 4, `src:near-full`, the remaining-conversation argument.
These are numerical facts for the displayed floor, not hypotheses about a
protocol frontier. Actual masses, stopping paths and subtree budgets still
have to be supplied by the constructed recursion.
-/

namespace Paper2.SourceSupportSchedule

noncomputable def floor (q : ℕ) (x : ℝ) (r : ℕ) : ℝ := 2 * (q : ℝ) * x / (2 : ℝ) ^ r

@[simp] theorem floor_zero (q : ℕ) (x : ℝ) : floor q x 0 = 2 * (q : ℝ) * x := by
  simp [floor]

theorem twice_next (q : ℕ) (x : ℝ) (r : ℕ) :
    2 * floor q x (r + 1) = floor q x r := by
  unfold floor
  rw [pow_succ]
  field_simp

theorem floor_pos {q : ℕ} {x : ℝ} (hq : 0 < q) (hx : 0 < x) (r : ℕ) :
    0 < floor q x r := by
  unfold floor
  positivity

theorem floor_antitone {q : ℕ} {x : ℝ} (hx : 0 ≤ x) : Antitone (floor q x) := by
  intro r t hrt
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hrt)

theorem floor_final (ell : ℕ) (x : ℝ) : floor (2 ^ ell) x (ell + 1) = x := by
  unfold floor
  rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ]
  field_simp

theorem threshold_le_floor {ell r : ℕ} {x : ℝ} (hx : 0 ≤ x) (hr : r ≤ ell + 1) :
    x ≤ floor (2 ^ ell) x r := by
  calc
    x = floor (2 ^ ell) x (ell + 1) := (floor_final ell x).symm
    _ ≤ floor (2 ^ ell) x r := floor_antitone hx hr

/-- After `r≤ell` Bob bits, the floor is twice the remaining dyadic capacity. -/
theorem floor_capacity (ell r : ℕ) (x : ℝ) (hr : r ≤ ell) :
    floor (2 ^ ell) x r = 2 * (2 : ℝ) ^ (ell - r) * x := by
  unfold floor
  rw [Nat.cast_pow, Nat.cast_ofNat,
    show (2 : ℝ) ^ ell = 2 ^ (ell - r) * 2 ^ r by
      rw [← pow_add, Nat.sub_add_cancel hr]]
  field_simp

/-- The finite-stage invariant keeps every unsplit attachment above half. -/
theorem attachment_mass_gt_half {q r : ℕ} {x m : ℝ}
    (hx : 0 ≤ x) (hsmall : floor q x 0 ≤ 1 / 8)
    (hm : 3 / 4 - floor q x 0 + floor q x r ≤ m) : 1 / 2 < m := by
  have hn : 0 ≤ floor q x r := by unfold floor; positivity
  linarith

/-- Integer rounding at capacity at least four supplies one more than
half the coordinate blocks, precisely the power-case row estimate's count. -/
theorem power_block_count {k h : ℕ} (hk : 2 ≤ k)
    (hh : (3 / 4 : ℝ) * (2 : ℝ) ^ k ≤ (h : ℝ)) :
    2 ^ (k - 1) + 1 ≤ h := by
  have he : (2 : ℝ) ^ k = 2 * (2 : ℝ) ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hb : 2 ≤ (2 : ℕ) ^ (k - 1) := by
    calc
      2 = (2 : ℕ) ^ 1 := by norm_num
      _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hn : 3 * (2 : ℕ) ^ (k - 1) ≤ 2 * h := by
    have ht : (3 : ℝ) * (2 : ℝ) ^ (k - 1) ≤ 2 * h := by rw [he] at hh; linarith
    exact_mod_cast ht
  omega

theorem two_block_count {h : ℕ} (hh : (3 / 4 : ℝ) * 2 ≤ (h : ℝ)) : 2 ≤ h := by
  have : 1 < (h : ℝ) := by linarith
  have : 1 < h := by exact_mod_cast this
  omega

/-- At capacity one, a single support with excess carries an attachment. -/
theorem single_support_attachment {h z : ℕ}
    (hh : (3 / 4 : ℝ) ≤ (h : ℝ)) (hexcess : 1 < h + z) (hz : z ≤ h)
    (hsmall : h < 2) : h = 1 ∧ z = 1 := by
  have hp : 0 < (h : ℝ) := by linarith
  have hn : 0 < h := by exact_mod_cast hp
  omega

end Paper2.SourceSupportSchedule

#print axioms Paper2.SourceSupportSchedule.threshold_le_floor
#print axioms Paper2.SourceSupportSchedule.floor_capacity
#print axioms Paper2.SourceSupportSchedule.attachment_mass_gt_half
#print axioms Paper2.SourceSupportSchedule.power_block_count
