import CurrentAdditive.QuarticExactLog

/-! The finite two-sided expansion for the actual printed v27 rectangle. -/

namespace CurrentAdditive.QuarticExactAsymptotics

open Paper2 Paper2.SourceProfileParameters Paper2.SourceRecursiveNoSampling

private theorem length_le_power (L : ℕ) (hL : 1 ≤ L) :
    L ≤ 2^(L-1) := by
  have hpow : ∀ n : ℕ, n+1 ≤ 2^n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        calc
          n+1+1 ≤ 2*(n+1) := by omega
          _ ≤ 2*2^n := Nat.mul_le_mul_left 2 ih
          _ = 2^(n+1) := by simp [pow_succ, mul_comm]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel_right] using hpow n

theorem source_budget_ge_length (L r q k : ℕ) (hk : 1 ≤ k) :
    L ≤ sourceBudget L r q k := by
  have hh : L ≤ exponent L + outerExponent L + exponent L + r + q := by
    dsimp [outerExponent]
    omega
  have hmul : exponent L + outerExponent L + exponent L + r + q ≤
      k * (exponent L + outerExponent L + exponent L + r + q) := by
    nlinarith [Nat.mul_le_mul_right
      (exponent L + outerExponent L + exponent L + r + q) hk]
  dsimp [sourceBudget]
  omega

theorem source_log_expansion (L r q k : ℕ)
    (hL : 1 ≤ L) (hk : 1 ≤ k) :
    let B := sourceBudget L r q k
    let T := sourceRows L r q k * sourceCols L r q k
    let p := 6*B+2*k-5
    let e : ℝ := Real.logb 2 (((L*T : ℕ) : ℝ) / (2^p : ℝ))
    0 ≤ e ∧ e ≤ Real.logb 2 (1 + 271/((2^(B-1):ℕ):ℝ)) ∧
      Real.logb 2 (T:ℝ) = (p:ℝ) - Real.logb 2 (L:ℝ) + e := by
  let B := sourceBudget L r q k
  have hB : 1 ≤ B := by dsimp [B, sourceBudget]; omega
  have hLB : L ≤ B := source_budget_ge_length L r q k hk
  have hLrank : L ≤ 2^(B-1) :=
    (length_le_power L hL).trans
      (Nat.pow_le_pow_right (by omega : 0 < (2:ℕ))
        (by omega : L-1 ≤ B-1))
  have hH : sourceCost L r q k = B+k := by
    dsimp [B, sourceCost, sourceBudget]
    ring
  have hT : sourceRows L r q k * sourceCols L r q k =
      Paper2.ReductionDimensions.entries
        (compressionEntropy (2^(B-1)) (B+k)) L := by
    dsimp [sourceRows, sourceCols, Paper2.ReductionDimensions.entries,
      sourceRank]
    rw [hH]
  have hh := entries_log_remainder_small B k L hB hL hLrank
  dsimp at hh ⊢
  rw [← hT] at hh
  exact hh

theorem printedT27_log_expansion (n m Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hn : 2 ≤ n) (hk : 1 ≤ k) :
    let L := Nat.clog 2 n
    let r := 4 * RestorationWidthScheduleScratch.ell L
    let q := CurrentAdditive.RandomizedSchedule.q27
      (V := Fin n) (E := Fin m) L γ Δ
    let B := sourceBudget L r q k
    let T := CurrentAdditive.QuarticAsymptotics.printedT27 n m Δ γ k
    let p := 6*B+2*k-5
    let e : ℝ := Real.logb 2 (((L*T : ℕ) : ℝ) / (2^p : ℝ))
    0 ≤ e ∧ e ≤ Real.logb 2 (1 + 271/((2^(B-1):ℕ):ℝ)) ∧
      Real.logb 2 (T:ℝ) = (p:ℝ) - Real.logb 2 (L:ℝ) + e := by
  have hL : 1 ≤ Nat.clog 2 n :=
    Nat.succ_le_of_lt (Nat.clog_pos (by decide) (by omega))
  simpa only [CurrentAdditive.QuarticAsymptotics.printedT27] using
    source_log_expansion (Nat.clog 2 n)
      (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n))
      (CurrentAdditive.RandomizedSchedule.q27
        (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ) k hL hk

end CurrentAdditive.QuarticExactAsymptotics
