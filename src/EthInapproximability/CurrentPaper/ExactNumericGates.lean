import EthInapproximability.CurrentPaper.ExactFiniteReduction

/-!
# Exact dyadic row thresholds

Source: frozen v8 `E-exact-details.tex` and `G-exact-control.tex`.
These are numerical consequences of the literal choices
`x = d⁻²`, `a₀ = 2^m/(2d)`, and `τ = ⌈2xN⌉`, where `d = 2^r`.
No communication bound or separation conclusion is assumed.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.ExactNumericGates

open ProtocolSeparation TerminalExcess

/-- The manuscript's row density `d⁻²`, for `d = 2^r`. -/
def rowDensity (r : ℕ) : ℝ := 1 / ((2 : ℝ) ^ r) ^ 2

/-- The excess-block density `2^m/(2d)`. -/
def excessDensity (r m : ℕ) : ℝ := (2 : ℝ) ^ m / (2 * (2 : ℝ) ^ r)

/-- The integer two-coordinate row threshold. -/
def pairThreshold (r N : ℕ) : ℕ := ⌈2 * rowDensity r * N⌉₊

private theorem scale_identity {r j : ℕ} (hj : j ≤ r) (e : ℕ) :
    ((2 : ℝ) ^ (r - j) * rowDensity r) * (2 : ℝ) ^ (j + e) =
      (2 : ℝ) ^ e / (2 : ℝ) ^ r := by
  have hp : (2 : ℝ) ^ (r - j) * (2 : ℝ) ^ j = (2 : ℝ) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hj]
  rw [pow_add]
  unfold rowDensity
  calc
    _ = ((2 : ℝ) ^ (r - j) * (2 : ℝ) ^ j) * (2 : ℝ) ^ e /
        ((2 : ℝ) ^ r) ^ 2 := by ring
    _ = (2 : ℝ) ^ e / (2 : ℝ) ^ r := by
      rw [hp]
      field_simp

/-- All even and odd Alice row thresholds follow from the same identity.
The offset is `0` for the even test and `1` for the odd test. -/
theorem row_threshold {r j e N : ℕ} (hj : j ≤ r) (he : e ≤ r) :
    ⌈(N : ℝ) * ((2 : ℝ) ^ (r - j) * rowDensity r)⌉₊ ≤
      rowThreshold N (j + e) := by
  unfold rowThreshold
  apply Nat.ceil_mono
  apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ (j + e))).2
  have hscaled : ((2 : ℝ) ^ (r - j) * rowDensity r) *
      (2 : ℝ) ^ (j + e) ≤ 1 := by
    rw [scale_identity hj]
    exact (div_le_one (by positivity)).2
      (pow_le_pow_right₀ (by norm_num) he)
  nlinarith [mul_le_mul_of_nonneg_left hscaled (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

/-- The one-block excess threshold contains the small-width row demand. -/
theorem base_row {r m N : ℕ} (hr : 1 ≤ r) :
    ⌈(N : ℝ) * ((2 : ℝ) ^ m * rowDensity r)⌉₊ ≤
      excessRows N (excessDensity r m) 0 := by
  unfold excessRows excessDensity rowDensity
  simp only [pow_zero, one_mul]
  apply Nat.ceil_mono
  have hd : (2 : ℝ) ≤ (2 : ℝ) ^ r := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr
  have hbase : 1 / ((2 : ℝ) ^ r) ^ 2 ≤ 1 / (2 * (2 : ℝ) ^ r) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hm : (0 : ℝ) ≤ (2 : ℝ) ^ m * N := by positivity
  convert mul_le_mul_of_nonneg_left hbase hm using 1 <;> ring

/-- Every higher excess threshold contains its indexed-projection demand. -/
theorem excess_row (r m N ell : ℕ) :
    ⌈(2 : ℝ) ^ (ell + m) * rowDensity r * (N : ℝ)⌉₊ ≤
      excessRows N (excessDensity r m) (ell + 1) := by
  unfold excessRows excessDensity rowDensity
  rw [pow_add, pow_succ]
  apply Nat.ceil_mono
  have hd : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
  have hbase : 1 / ((2 : ℝ) ^ r) ^ 2 ≤ 1 / (2 : ℝ) ^ r := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hbase
    (show (0 : ℝ) ≤ (2 : ℝ) ^ ell * (2 : ℝ) ^ m * N by positivity)
  convert hmul using 1 <;> ring

/-- At the terminal level the manuscript's excess and Alice thresholds
are equal, so there is no ceiling-rounding loss. -/
theorem excess_final {r m j N : ℕ} (hj : j ≤ r) (hm : m ≤ r - j) :
    excessRows N (excessDensity r m) (r - j - m) = rowThreshold N (j + 1) := by
  unfold excessRows excessDensity rowThreshold
  congr 1
  have hp : (2 : ℝ) ^ (r - j - m) * (2 : ℝ) ^ m * (2 : ℝ) ^ j =
      (2 : ℝ) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hm, ← pow_add, Nat.sub_add_cancel hj]
  rw [pow_succ]
  field_simp
  nlinarith [congrArg (fun z : ℝ => z * (N : ℝ)) hp]

/-- All six row and excess gates in `NumericParameters`, for literal
paper densities. The small/large side conditions are not needed numerically. -/
theorem row_gates {r m N : ℕ} (hr : 1 ≤ r) :
    (∀ j, j < r → r - j ≤ m →
      ⌈(N : ℝ) * ((2 : ℝ) ^ (r - j) * rowDensity r)⌉₊ ≤ rowThreshold N j) ∧
    (∀ j, j + 1 < r → r - j ≤ m →
      ⌈(N : ℝ) * ((2 : ℝ) ^ (r - j) * rowDensity r)⌉₊ ≤ rowThreshold N (j + 1)) ∧
    (∀ j, j < r → m ≤ r - j →
      ⌈(2 : ℝ) ^ (r - j) * rowDensity r * (N : ℝ)⌉₊ ≤ rowThreshold N j) ∧
    ⌈(N : ℝ) * ((2 : ℝ) ^ m * rowDensity r)⌉₊ ≤ excessRows N (excessDensity r m) 0 ∧
    (∀ ell, ell < r - m →
      ⌈(2 : ℝ) ^ (ell + m) * rowDensity r * (N : ℝ)⌉₊ ≤
        excessRows N (excessDensity r m) (ell + 1)) ∧
    (∀ j, j + 1 < r → m < r - j →
      excessRows N (excessDensity r m) (r - j - m) ≤ rowThreshold N (j + 1)) := by
  refine ⟨?_, ?_, ?_, base_row hr, ?_, ?_⟩
  · intro j hj _
    simpa using row_threshold (N := N) (e := 0) (by omega : j ≤ r) (Nat.zero_le r)
  · intro j hj _
    exact row_threshold (by omega) hr
  · intro j hj _
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      row_threshold (N := N) (e := 0) (by omega : j ≤ r) (Nat.zero_le r)
  · intro ell _
    exact excess_row r m N ell
  · intro j hj hm
    exact (excess_final (by omega : j ≤ r) (by omega : m ≤ r - j)).le

/-- Positivity and the basic row-scale bounds for the literal density. -/
theorem density_gates {r m : ℕ} (hr : 1 ≤ r) (hm : m ≤ r) :
    0 < rowDensity r ∧ rowDensity r ≤ 1 ∧
      (2 : ℝ) ^ m * rowDensity r ≤ 1 ∧
      (2 : ℝ) ^ r * rowDensity r < 1 ∧ 0 ≤ excessDensity r m := by
  have hd : (2 : ℝ) ≤ (2 : ℝ) ^ r := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr
  have hm' : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ r :=
    pow_le_pow_right₀ (by norm_num) hm
  have hdpos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  unfold rowDensity excessDensity
  refine ⟨by positivity, ?_, ?_, ?_, by positivity⟩
  · exact (div_le_one (by positivity)).2 (by nlinarith)
  · rw [mul_one_div]
    exact (div_le_one (by positivity)).2 (by nlinarith)
  · rw [mul_one_div]
    exact (div_lt_one (by positivity)).2 (by nlinarith)

/-- Ceiling rounding costs less than a quarter of all labels once
`d ≥ 16` and `N ≥ d²`. The actual family has the stronger `N ≥ d⁶⁴`. -/
theorem pair_loss {r N : ℕ} (hr : 4 ≤ r) (hN : (2 ^ r) ^ 2 ≤ N) :
    (2 : ℝ) ^ r * (pairThreshold r N : ℝ) < (N : ℝ) / 4 := by
  have hd : (16 : ℝ) ≤ (2 : ℝ) ^ r := by
    convert pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr using 1
    norm_num
  have hNR : ((2 : ℝ) ^ r) ^ 2 ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by nlinarith
  have hc := Nat.ceil_lt_add_one (R := ℝ)
    (show 0 ≤ 2 * rowDensity r * (N : ℝ) by unfold rowDensity; positivity)
  have hscaled : ((2 : ℝ) ^ r) ^ 2 * (pairThreshold r N : ℝ) <
      2 * (N : ℝ) + ((2 : ℝ) ^ r) ^ 2 := by
    calc
      _ < ((2 : ℝ) ^ r) ^ 2 * (2 * rowDensity r * N + 1) :=
        mul_lt_mul_of_pos_left hc (by positivity)
      _ = _ := by unfold rowDensity; field_simp
  have hfactor : 16 * (2 : ℝ) ^ r ≤ ((2 : ℝ) ^ r) ^ 2 := by nlinarith
  have hbound := mul_le_mul_of_nonneg_right hfactor
    (show (0 : ℝ) ≤ (pairThreshold r N : ℝ) by positivity)
  nlinarith

/-- The integer pair threshold is positive, meets the projection demand,
and satisfies the strict coordinate-separation gate. -/
theorem pair_gates {r N : ℕ} (hr : 4 ≤ r) (hN : (2 ^ r) ^ 2 ≤ N) :
    ⌈(N : ℝ) * (2 * rowDensity r)⌉₊ ≤ pairThreshold r N ∧
      1 ≤ pairThreshold r N ∧ 2 ^ r * pairThreshold r N < N := by
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  refine ⟨by unfold pairThreshold; rw [mul_comm], ?_, ?_⟩
  · exact Nat.ceil_pos.mpr (by unfold rowDensity; positivity)
  · have hp := pair_loss hr hN
    have hNnonneg : (0 : ℝ) ≤ N := by positivity
    have hgap : (2 : ℝ) ^ r * (pairThreshold r N : ℝ) < (N : ℝ) := by linarith
    exact_mod_cast hgap

/-- The actual retained-row density exceeds the one-copy balance test.
The modest `ε ≤ 1/4` bound is implied by the paper's `ε = d⁻⁸`. -/
theorem retained_density {r N : ℕ} {ε : ℝ} (hr : 4 ≤ r)
    (hN : (2 ^ r) ^ 2 ≤ N) (hε : ε ≤ 1 / 4) :
    (1 + ε) * (N : ℝ) / 2 <
      ((N - (2 ^ r - 1) * pairThreshold r N : ℕ) : ℝ) := by
  have hp := pair_loss hr hN
  have hgap := (pair_gates hr hN).2.2
  have hloss : (2 ^ r - 1) * pairThreshold r N ≤ 2 ^ r * pairThreshold r N :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hsub : (2 ^ r - 1) * pairThreshold r N ≤ N := by omega
  have hlossR : (((2 ^ r - 1) * pairThreshold r N : ℕ) : ℝ) ≤
      (2 : ℝ) ^ r * (pairThreshold r N : ℝ) := by exact_mod_cast hloss
  rw [Nat.cast_sub hsub]
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < (2 ^ r) ^ 2) hN)
  have hεN := mul_le_mul_of_nonneg_right hε hNpos.le
  nlinarith

private theorem scaled_copy_count {r m : ℕ} (hm : 5 ≤ m) (hmr : m ≤ r) :
    ((2 ^ (r - m) * HardSeed.copyCount m : ℕ) : ℝ) =
      9 * (2 : ℝ) ^ r / 16 := by
  have hexp : r - m + (m - 5) + 5 = r := by omega
  have hp : 32 * ((2 : ℝ) ^ (r - m) * (2 : ℝ) ^ (m - 5)) = (2 : ℝ) ^ r := by
    calc
      _ = (2 : ℝ) ^ (r - m + (m - 5) + 5) := by
        rw [pow_add, pow_add]
        norm_num
        ring
      _ = _ := by rw [hexp]
  simp only [HardSeed.copyCount, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  nlinarith

private theorem full_fraction {d : ℝ} (hd : 32 ≤ d) :
    9 * d / 16 ≤ d * ((3 / 5 : ℝ) - 1 / d) / (1 - 1 / d) := by
  have hdpos : 0 < d := by linarith
  have hx : 1 / d < 1 := (div_lt_one hdpos).2 (by linarith)
  apply (le_div_iff₀ (by linarith : 0 < 1 - 1 / d)).2
  have he : d * ((3 / 5 : ℝ) - 1 / d) -
      (9 * d / 16) * (1 - 1 / d) = (3 * d - 35) / 80 := by
    field_simp
    ring
  linarith

private theorem half_fraction {d : ℝ} (hd : 32 ≤ d) :
    9 * d / 32 ≤ d * ((3 / 10 : ℝ) - 1 / (2 * d)) / (1 - 1 / (2 * d)) := by
  have hdpos : 0 < 2 * d := by linarith
  have hx : 1 / (2 * d) < 1 := (div_lt_one hdpos).2 (by linarith)
  apply (le_div_iff₀ (by linarith : 0 < 1 - 1 / (2 * d))).2
  have he : d * ((3 / 10 : ℝ) - 1 / (2 * d)) -
      (9 * d / 32) * (1 - 1 / (2 * d)) = (6 * d - 115) / 320 := by
    field_simp
    ring
  linarith

/-- The two dense-block counts needed for the first and second profiles
are satisfied by the manuscript's exact `9t/16` copy count. -/
theorem coordinate_gates {r m : ℕ} (hr : 5 ≤ r) (hm : 5 ≤ m)
    (hmr : m + 1 ≤ r) :
    (2 ^ (r - m) * HardSeed.copyCount m ≤
      ⌈(2 : ℝ) ^ r * ((3 / 5 : ℝ) - (2 : ℝ) ^ r * rowDensity r) /
        (1 - (2 : ℝ) ^ r * rowDensity r)⌉₊) ∧
    (2 ^ (r - m - 1) * HardSeed.copyCount m ≤
      ⌈(2 : ℝ) ^ r * ((3 / 10 : ℝ) - (2 : ℝ) ^ (r - 1) * rowDensity r) /
        (1 - (2 : ℝ) ^ (r - 1) * rowDensity r)⌉₊) := by
  have hd : (32 : ℝ) ≤ (2 : ℝ) ^ r := by
    convert pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr using 1
    norm_num
  have hfull : (2 : ℝ) ^ r * rowDensity r = 1 / (2 : ℝ) ^ r := by
    unfold rowDensity
    field_simp
  have hp : 2 * (2 : ℝ) ^ (r - 1) = (2 : ℝ) ^ r := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ r)]
  have hhalf : (2 : ℝ) ^ (r - 1) * rowDensity r = 1 / (2 * (2 : ℝ) ^ r) := by
    unfold rowDensity
    field_simp
    nlinarith
  constructor
  · rw [hfull]
    have hc := scaled_copy_count hm (by omega : m ≤ r)
    have hb := full_fraction hd
    have hceil := Nat.le_ceil ((2 : ℝ) ^ r * ((3 / 5 : ℝ) - 1 / (2 : ℝ) ^ r) /
      (1 - 1 / (2 : ℝ) ^ r))
    have hout : ((2 ^ (r - m) * HardSeed.copyCount m : ℕ) : ℝ) ≤
        (⌈(2 : ℝ) ^ r * ((3 / 5 : ℝ) - 1 / (2 : ℝ) ^ r) /
          (1 - 1 / (2 : ℝ) ^ r)⌉₊ : ℝ) := by linarith
    exact_mod_cast hout
  · rw [hhalf]
    have hc := scaled_copy_count hm (by omega : m ≤ r - 1)
    have he : r - 1 - m = r - m - 1 := by omega
    rw [he] at hc
    have hb := half_fraction hd
    have hceil := Nat.le_ceil ((2 : ℝ) ^ r * ((3 / 10 : ℝ) - 1 / (2 * (2 : ℝ) ^ r)) /
      (1 - 1 / (2 * (2 : ℝ) ^ r)))
    have hout : ((2 ^ (r - m - 1) * HardSeed.copyCount m : ℕ) : ℝ) ≤
        (⌈(2 : ℝ) ^ r * ((3 / 10 : ℝ) - 1 / (2 * (2 : ℝ) ^ r)) /
          (1 - 1 / (2 * (2 : ℝ) ^ r))⌉₊ : ℝ) := by linarith
    exact_mod_cast hout

end EthInapproximability.CurrentPaper.ExactNumericGates
