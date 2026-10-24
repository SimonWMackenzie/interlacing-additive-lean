import EthInapproximability.CurrentPaper.SlowClock
import EthInapproximability.CurrentPaper.FinalPadding

/-!
# The bounded clock and the common padding exponent

Source: locked v8 `05-iteration.tex`, `lem:paper-slow-diagonal`, and
`06-eth.tex`, `eq:paper-common-padding-scale`,
`eq:paper-table-subexponential`, `eq:paper-length-clock-allowance`, and
`eq:paper-length-clock-gap-fit`.

The clock is the literal bounded prefix scan in `SlowClock`, and the padding
exponent and allowance are the formulas in `FinalPadding`. Termination of
the supplied cutoff machine is an explicit input. The module does not
instantiate that machine or establish a bit-time simulation bound.
-/

namespace EthInapproximability.CurrentPaper.ClockedPadding

open SlowClock

variable {State : Type*}

theorem allowance_monotone (M : Machine State) :
    Monotone (FinalPadding.allowance (repetitions M)) :=
  FinalPadding.allowance_monotone _ (repetitions_mono M)

theorem allowance_unbounded (M : Machine State) (hterm : Terminates M) :
    ∀ K, ∃ T, K ≤ FinalPadding.allowance (repetitions M) T := by
  apply FinalPadding.allowance_unbounded _ (repetitions_mono M)
  intro K
  obtain ⟨N, hN⟩ := repetitions_unbounded M hterm K
  exact ⟨N, hN N le_rfl⟩

theorem allowance_tendsto_atTop (M : Machine State) (hterm : Terminates M) :
    Filter.Tendsto (FinalPadding.allowance (repetitions M))
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro K
  obtain ⟨N, hN⟩ := allowance_unbounded M hterm K
  exact ⟨N, fun n hn => hN.trans (allowance_monotone M hn)⟩

/-- The floor in the common padding exponent can only improve the bound. -/
theorem exponent_ratio_le (M : Machine State) (n : ℕ)
    (hn : 0 < n) (hk : 0 < repetitions M n) :
    (FinalPadding.exponent (repetitions M) n : ℝ) / n ≤
      1 / (2 * (repetitions M n : ℝ)) := by
  have hprod : FinalPadding.exponent (repetitions M) n *
      (2 * repetitions M n) ≤ n := by
    simpa only [FinalPadding.exponent, max_eq_right (show 1 ≤ repetitions M n by omega)] using
      Nat.div_mul_le_self n (2 * repetitions M n)
  have hreal : (FinalPadding.exponent (repetitions M) n : ℝ) *
      (2 * (repetitions M n : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hprod
  apply (div_le_div_iff₀ (by exact_mod_cast hn)
    (by positivity : (0 : ℝ) < 2 * (repetitions M n : ℝ))).2
  simpa using hreal

/-- The actual selected exponent, divided by the source parameter, tends
to zero. No fixed-level estimate is substituted at an unbounded level. -/
theorem exponent_ratio_tendsto_zero (M : Machine State) (hterm : Terminates M) :
    Filter.Tendsto
      (fun n => (FinalPadding.exponent (repetitions M) n : ℝ) / n)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
    (Filter.Eventually.of_forall (fun n => by positivity))
    _ (reciprocal_repetitions_tendsto_zero M hterm)
  obtain ⟨N, hN⟩ := repetitions_unbounded M hterm 1
  apply Filter.eventually_atTop.mpr
  refine ⟨max N 1, fun n hn => ?_⟩
  exact exponent_ratio_le M n (by omega) (by have := hN n (by omega); omega)

/-- The logarithm of the actual power-of-two table length has no small-input
exception. The separate `max T 2` in the allowance does have one. -/
theorem log_tableSize (M : Machine State) (n : ℕ) :
    Nat.log 2 (FinalPadding.tableSize (repetitions M) n) =
      2 * FinalPadding.exponent (repetitions M) n := by
  exact Nat.log_pow (by omega : 1 < 2) _

/-- The base-two logarithm of the common table length is sublinear in the
source parameter. This is a size statement, not a materialization runtime. -/
theorem log_tableSize_ratio_tendsto_zero (M : Machine State)
    (hterm : Terminates M) :
    Filter.Tendsto
      (fun n => (Nat.log 2 (FinalPadding.tableSize (repetitions M) n) : ℝ) / n)
      Filter.atTop (nhds 0) := by
  have h := (exponent_ratio_tendsto_zero M hterm).const_mul (2 : ℝ)
  simpa only [log_tableSize, Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc,
    mul_zero] using h

/-- A concrete numerical property of returned cutoffs, rather than a
padding or gap conclusion. The paper's cutoff implementation must establish
any use of this stronger output bound. -/
def DoubledCutoffs (M : Machine State) : Prop :=
  ∀ fuel k cutoff, 1 ≤ k → M.output (run M fuel k) = some cutoff →
    2 * k ≤ cutoff

theorem twice_repetitions_le (M : Machine State) (hout : DoubledCutoffs M)
    (n : ℕ) (hk : 0 < repetitions M n) : 2 * repetitions M n ≤ n := by
  obtain ⟨cutoff, hr, hc⟩ := selected_run M n (repetitions M n) hk le_rfl
  exact (hout n (repetitions M n) cutoff hk hr).trans hc

/-- This proves, rather than assumes, the guard required by the generic
logarithm identity when doubled cutoffs are available. -/
theorem exponent_pos (M : Machine State) (hout : DoubledCutoffs M)
    (n : ℕ) (hk : 0 < repetitions M n) :
    0 < FinalPadding.exponent (repetitions M) n := by
  unfold FinalPadding.exponent
  rw [max_eq_right (show 1 ≤ repetitions M n by omega)]
  exact Nat.div_pos (twice_repetitions_le M hout n hk) (by omega)

theorem exponent_eventually_pos (M : Machine State) (hterm : Terminates M)
    (hout : DoubledCutoffs M) :
    ∀ᶠ n in Filter.atTop, 0 < FinalPadding.exponent (repetitions M) n := by
  obtain ⟨N, hN⟩ := repetitions_unbounded M hterm 1
  exact Filter.eventually_atTop.mpr ⟨N, fun n hn =>
    exponent_pos M hout n (by have := hN n hn; omega)⟩

/-- The special small-table convention causes no error for this actual
clock: at budget one, at most one input can have been selected. -/
theorem allowance_one (M : Machine State) :
    FinalPadding.allowance (repetitions M) 1 = 0 := by
  have h := repetitions_le M 1
  change repetitions M 1 / 4 = 0
  omega

/-- For the literal bounded clock the desired gap fits even in the zero
exponent branch: that branch has a one-bit table and allowance zero. This
does not remove the positive-exponent guard from the generic log identity. -/
theorem gap_fit (M : Machine State) (n : ℕ) (hk : 0 < repetitions M n) :
    2 * FinalPadding.allowance (repetitions M)
      (FinalPadding.tableSize (repetitions M) n) < repetitions M n := by
  by_cases hp : 0 < FinalPadding.exponent (repetitions M) n
  · exact FinalPadding.gap_fit _ (repetitions_mono M) n hk hp
  · have hp0 : FinalPadding.exponent (repetitions M) n = 0 := by omega
    simp only [FinalPadding.tableSize, hp0, mul_zero, pow_zero, allowance_one,
      mul_zero]
    exact hk

theorem gap_fit_eventually (M : Machine State) (hterm : Terminates M) :
    ∀ᶠ n in Filter.atTop,
      2 * FinalPadding.allowance (repetitions M)
        (FinalPadding.tableSize (repetitions M) n) < repetitions M n := by
  obtain ⟨N, hN⟩ := repetitions_unbounded M hterm 1
  exact Filter.eventually_atTop.mpr ⟨N, fun n hn =>
    gap_fit M n (by have := hN n hn; omega)⟩

end EthInapproximability.CurrentPaper.ClockedPadding
