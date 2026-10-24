import Paper2.SamplingBounds
import Paper2.SquarePadding

/-!
# Finite bounds on the exact final sample dimensions

Frozen v12, `sections/06-reduction.tex`, `eq:final-dimensions`, the
uniform-reduction proof and the final square-padding paragraph.
The quantities below are exactly the public integer sample counts. These
lemmas do not assert a generator runtime or the sharp asymptotic coefficient
six; they supply finite size and aspect-ratio bounds for those later proofs.
-/

namespace Paper2.ReductionDimensions

/-- Number of entries in the actual indexed rectangular output. -/
def entries (Z L : ℕ) : ℕ := compressionRowDraws Z L * compressionColumnDraws Z

theorem rowDraws_le (Z L : ℕ) (hL : 1 ≤ L) : compressionRowDraws Z L ≤ Z + 12 := by
  apply (ceilDiv_le_iff_le_mul (by omega : 0 < L)).mpr
  nlinarith

theorem rowDraws_le_columnDraws (Z L : ℕ) (hL : 1 ≤ L) :
    compressionRowDraws Z L ≤ compressionColumnDraws Z := by
  have := rowDraws_le Z L hL
  unfold compressionColumnDraws
  omega

/-- The rectangular aspect ratio is at most `2L`, including all ceilings. -/
theorem columnDraws_le_twiceL_rows (Z L : ℕ) (hL : 1 ≤ L) :
    compressionColumnDraws Z ≤ (2 * L) * compressionRowDraws Z L := by
  have h := compressionRowDraws_cover Z L hL
  unfold compressionColumnDraws
  nlinarith

/-- Hence square padding multiplies the actual entry count by less than
`8L`, rather than squaring an arbitrary polynomial bound. -/
theorem square_entries_lt (Z L : ℕ) (hL : 1 ≤ L) :
    SquarePadding.entries (compressionRowDraws Z L) (compressionColumnDraws Z) <
      8 * L * entries Z L := by
  have h := SquarePadding.entries_lt_four_ratio
    (show 0 < compressionColumnDraws Z by unfold compressionColumnDraws; omega)
    (rowDraws_le_columnDraws Z L hL) (columnDraws_le_twiceL_rows Z L hL)
  simpa only [entries, show 4 * (2 * L) = 8 * L by omega] using h

/-- The sample entropy is bounded using the public rank and depth budgets. -/
theorem entropy_le_pow (B H : ℕ) :
    compressionEntropy (2 ^ (B - 1)) H ≤ 2 ^ (2 * B + H + 2) := by
  have hr : 2 ^ (B - 1) ≤ 2 ^ B := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have hp : 1 ≤ 2 ^ B := Nat.one_le_two_pow
  have hfactor : 2 ^ (B - 1) * (2 ^ (B - 1) + 1) + 2 ≤ 4 * (2 ^ B) ^ 2 := by
    have hmul := Nat.mul_le_mul hr (Nat.add_le_add_right hr 1)
    nlinarith
  have hH : 2 ^ (H - 1) ≤ 2 ^ H := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  calc
    _ ≤ (4 * (2 ^ B) ^ 2) * 2 ^ H := Nat.mul_le_mul hfactor hH
    _ = _ := by
      rw [show 2 * B + H + 2 = B + B + H + 2 by omega]
      simp only [pow_add]
      ring

theorem entropy_slack_le_pow (B H : ℕ) :
    compressionEntropy (2 ^ (B - 1)) H + 12 ≤ 2 ^ (2 * B + H + 6) := by
  have h := entropy_le_pow B H
  have hp : 1 ≤ 2 ^ (2 * B + H + 2) := Nat.one_le_two_pow
  have he : 2 * B + H + 6 = (2 * B + H + 2) + 4 := by omega
  rw [he, pow_add]
  norm_num
  omega

theorem columnDraws_le_pow (B H : ℕ) :
    compressionColumnDraws (compressionEntropy (2 ^ (B - 1)) H) ≤
      2 ^ (2 * B + H + 7) := by
  have h := entropy_slack_le_pow B H
  have he : 2 * B + H + 7 = (2 * B + H + 6) + 1 := by omega
  rw [he, pow_succ]
  unfold compressionColumnDraws
  omega

theorem entries_le_pow (B H L : ℕ) (hL : 1 ≤ L) :
    entries (compressionEntropy (2 ^ (B - 1)) H) L ≤
      2 ^ (4 * B + 2 * H + 14) := by
  have hc := columnDraws_le_pow B H
  have hr := (rowDraws_le_columnDraws (compressionEntropy (2 ^ (B - 1)) H) L hL).trans hc
  apply (Nat.mul_le_mul hr hc).trans_eq
  rw [← pow_add]
  congr 1
  omega

/-- Elementary budgets used by the uniform algorithm, not an asymptotic
choice of the number of iterations. -/
theorem iteration_budgets (d₀ h k L : ℕ) (hd : d₀ ≤ L) (hh : h ≤ 7 * L)
    (hL : 1 ≤ L) :
    d₀ + k * h ≤ (7 * k + 1) * L ∧
      d₀ + k * h + k ≤ (8 * k + 1) * L := by
  constructor <;> nlinarith

/-- An explicit exponent independent of the iteration count. This is an
output-length bound for the exact public counts, not a runtime theorem. -/
theorem entries_uniform_bound (d₀ h k L : ℕ) (hd : d₀ ≤ L) (hh : h ≤ 7 * L)
    (hL : 1 ≤ L) :
    entries (compressionEntropy (2 ^ (d₀ + k * h - 1)) (d₀ + k * h + k)) L ≤
      2 ^ (58 * (k + 1) * L) := by
  have hb := iteration_budgets d₀ h k L hd hh hL
  apply (entries_le_pow (d₀ + k * h) (d₀ + k * h + k) L hL).trans
  apply Nat.pow_le_pow_right (by decide)
  nlinarith

end Paper2.ReductionDimensions
