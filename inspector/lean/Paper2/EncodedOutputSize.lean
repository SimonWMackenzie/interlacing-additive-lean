import Paper2.EncodedSelectedOutput
import Paper2.TotalFiniteResources

/-! Literal encoded selected-output length, including all binary headers. -/

namespace Paper2.EncodedOutputSize

open Paper2.TotalFiniteConstructorScratch
  Paper2.TotalFiniteResourcesScratch
  Paper2.EncodedSelectedOutput
  Paper2.SourceRecursiveNoSampling
  Paper2.ParameterizedCanonicalSource
  Paper2.SourceProfileParameters

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

private theorem bits_length_le_succ (x : ℕ) : x.bits.length ≤ x + 1 := by
  have hpow : x < 2 ^ (x + 1) := by
    have h := Paper2.WidthDomination.nat_le_two_pow x
    have hp : 0 < 2 ^ x := pow_pos (by omega) _
    rw [pow_succ]
    omega
  simpa only [Nat.size_eq_bits_len] using (Nat.size_le.mpr hpow)

private theorem scheduled_budget_le_resource {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ) :
    (scheduledOutput hn edge Δ γ k hc).budget ≤ resourceBound n k := by
  let L := Nat.clog 2 n
  let d₀ := LookupSeed.exponent L + 1
  let h := Paper2.SourceOverheadBounds.overhead
    (V := Fin n) (E := Fin m) L Δ γ
  have hc' := hc
  rcases hc' with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hover, hL, hseed⟩
  have hL1 : 1 ≤ L := by omega
  have hB := Paper2.ReductionDimensions.iteration_budgets
    d₀ h k L hseed hover hL1
  have hbudget : (scheduledOutput hn edge Δ γ k hc).budget = d₀ + k * h := by
    dsimp [scheduledOutput, sourceBudget, d₀, h,
      Paper2.SourceOverheadBounds.overhead,
      ParameterizedCanonicalSource.restorationDepth,
      ParameterizedCanonicalSource.coverDepth]
  have hB' : (scheduledOutput hn edge Δ γ k hc).budget ≤
      8 * (k + 1) * L := by
    rw [hbudget]
    nlinarith only [hB.1]
  have hbase : 2 ^ L ≤ (n + 2) ^ 2 := by
    have hd := CappedSampler.ticketSize_le_twice n hn
    change 2 ^ L ≤ 2 * n at hd
    have hn2 : 2 * n ≤ (n + 2) ^ 2 := by
      calc
        2 * n ≤ n * n + 4 * n + 4 := by omega
        _ = (n + 2) ^ 2 := by ring
    exact hd.trans hn2
  have hpow := Nat.pow_le_pow_left hbase (8 * (k + 1))
  have hExp : 16 * (k + 1) ≤ 160 * (k + 1) := by omega
  calc
    _ ≤ 8 * (k + 1) * L := hB'
    _ ≤ 2 ^ (8 * (k + 1) * L) := Paper2.WidthDomination.nat_le_two_pow _
    _ = (2 ^ L) ^ (8 * (k + 1)) := by
      rw [← pow_mul]
      congr 1
      ring
    _ ≤ ((n + 2) ^ 2) ^ (8 * (k + 1)) := hpow
    _ = (n + 2) ^ (16 * (k + 1)) := by
      rw [← pow_mul]
      congr 1
      ring
    _ ≤ resourceBound n k := by
      dsimp [resourceBound]
      exact pow_le_pow_right₀ (by omega) hExp

theorem selected_budget_le_resource {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    (select hn edge Δ γ k).budget ≤ resourceBound n k := by
  by_cases hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ
  · rw [select_good hn edge Δ γ k hc]
    exact scheduled_budget_le_resource hn edge Δ γ k hc
  · rw [select_bad hn edge Δ γ k hc]
    simp only [fallbackOutput]
    exact Nat.zero_le _

/-- The selected *encoded* output list includes all three variable-length
binary fields and the literal table, on every selected tape and branch. -/
theorem outputBits_length_le_poly {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (hk : 1 ≤ k)
    (t : (select hn edge Δ γ k).Tape) :
    (outputBits hn edge Δ γ k t).length ≤
      (n + 2) ^ (164 * (k + 1)) := by
  let o := select hn edge Δ γ k
  let R := resourceBound n k
  have hdims := selected_dimensions_pos hn edge Δ γ k
  have hcounts := selected_announced_counts_le hn edge Δ γ k hk
  have hbudget := selected_budget_le_resource hn edge Δ γ k
  have hrows : o.rows ≤ R := by
    have h := Nat.mul_le_mul_left o.rows hdims.2
    dsimp [o, R] at *
    omega
  have hcols : o.cols ≤ R := by
    have h := Nat.mul_le_mul_right o.cols hdims.1
    dsimp [o, R] at *
    nlinarith only [h, hcounts.1]
  have hR : 1 ≤ R := by
    dsimp [R, resourceBound]
    have hp : 0 < (n + 2) ^ (160 * (k + 1)) := pow_pos (by omega) _
    omega
  have hbitsR : o.rows.bits.length ≤ R + 1 :=
    (bits_length_le_succ o.rows).trans (Nat.add_le_add_right hrows 1)
  have hbitsC : o.cols.bits.length ≤ R + 1 :=
    (bits_length_le_succ o.cols).trans (Nat.add_le_add_right hcols 1)
  have hbitsB : o.budget.bits.length ≤ R + 1 :=
    (bits_length_le_succ o.budget).trans (Nat.add_le_add_right hbudget 1)
  have hlength : (outputBits hn edge Δ γ k t).length ≤ 7 * R + 9 := by
    have heq := outputBits_length hn edge Δ γ k t
    dsimp only at heq
    rw [heq]
    dsimp [o, R] at *
    omega
  have h16 : 7 * R + 9 ≤ 16 * R := by omega
  have hbase : 16 ≤ (n + 2) ^ 4 := by
    have hb : 2 ≤ n + 2 := by omega
    have h := Nat.pow_le_pow_left hb 4
    norm_num at h ⊢
    exact h
  have hpow := Nat.mul_le_mul_left R hbase
  have hExp : 160 * (k + 1) + 4 ≤ 164 * (k + 1) := by omega
  calc
    _ ≤ 7 * R + 9 := hlength
    _ ≤ 16 * R := h16
    _ ≤ R * (n + 2) ^ 4 := by nlinarith only [hpow]
    _ = (n + 2) ^ (160 * (k + 1) + 4) := by
      dsimp [R, resourceBound]
      rw [pow_add]
    _ ≤ (n + 2) ^ (164 * (k + 1)) :=
      pow_le_pow_right₀ (by omega) hExp

end Paper2.EncodedOutputSize
