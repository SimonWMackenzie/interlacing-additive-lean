import CurrentAdditive.QuarticSourceTapeFit
import CurrentAdditive.QuarticClockB
import Paper2.EncodedOutputSize

/-! Fixed-polynomial length of the literal v27 encoded selected instance. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.TotalFiniteResourcesScratch

private theorem bits_length_le_succ27 (x : ℕ) : x.bits.length ≤ x + 1 := by
  have hpow : x < 2 ^ (x + 1) := by
    have h := Paper2.WidthDomination.nat_le_two_pow x
    have hp : 0 < 2 ^ x := pow_pos (by omega) _
    rw [pow_succ]
    omega
  simpa only [Nat.size_eq_bits_len] using (Nat.size_le.mpr hpow)

theorem selected_budget_le_resource27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    (select27 hn edge Δ γ k).budget ≤ resourceBound n k := by
  by_cases hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ
  · letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    rw [select27_good hn edge Δ γ k hc]
    have hb := Paper2.CurrentAdditive.QuarticClockB.budget_cap27 Δ γ hc k
    have hconv := Paper2.A3Assembly.Clock.two_pow_mul_clog_le 29 k n
    rw [show 2 * 29 * (k + 1) = 58 * (k + 1) by ring] at hconv
    rw [show 29 * ((k + 1) * Nat.clog 2 n) =
      29 * (k + 1) * Nat.clog 2 n by ring] at hb
    calc
      _ ≤ 2 ^ (29 * (k + 1) * Nat.clog 2 n) := hb
      _ ≤ (n + 2) ^ (58 * (k + 1)) := hconv
      _ ≤ resourceBound n k := by
        dsimp [resourceBound]
        exact pow_le_pow_right₀ (by omega) (by omega)
  · rw [select27_bad hn edge Δ γ k hc]
    simp only [TotalFiniteConstructorScratch.fallbackOutput]
    exact Nat.zero_le _

theorem outputBits27_length_le_poly {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (hk : 1 ≤ k)
    (t : (select27 hn edge Δ γ k).Tape) :
    (outputBits27 hn edge Δ γ k t).length ≤
      (n + 2) ^ (164 * (k + 1)) := by
  let o := select27 hn edge Δ γ k
  let R := resourceBound n k
  have hdims := select27_dimensions_pos hn edge Δ γ k
  have hcounts := QuarticInputSize.selected_announced_counts_le27 hn edge Δ γ k hk
  have hbudget := selected_budget_le_resource27 hn edge Δ γ k
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
    (bits_length_le_succ27 o.rows).trans (Nat.add_le_add_right hrows 1)
  have hbitsC : o.cols.bits.length ≤ R + 1 :=
    (bits_length_le_succ27 o.cols).trans (Nat.add_le_add_right hcols 1)
  have hbitsB : o.budget.bits.length ≤ R + 1 :=
    (bits_length_le_succ27 o.budget).trans (Nat.add_le_add_right hbudget 1)
  have hlength : (outputBits27 hn edge Δ γ k t).length ≤ 7 * R + 9 := by
    have heq := outputBits27_length hn edge Δ γ k t
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

#print axioms selected_budget_le_resource27
#print axioms outputBits27_length_le_poly

end Paper2.CurrentAdditive.QuarticClassEndpoint
