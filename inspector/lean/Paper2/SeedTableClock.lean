import Paper2.SeedBitEntry
import Paper2.FrontClockA
import Paper2.LookupSeed
import EthInapproximability.CurrentPaper.MatrixTableWriter

/-!
# WP-SEED, part 3: the polynomial clock (pure arithmetic)

Lane `owner:a-seed-t45-1`. Bounds the explicit clock of the seed-table run by
`seedC * (n+1)^1536` for every `n ≥ 4`, using the admitted `FrontClock13.lBd_le`,
`FrontClock13.clog_sq_le`, `LookupSeed.rows_source_bound` and
`MatrixTableWriter.writerBound_polynomial`.
-/

namespace SeedT45.SeedClock

noncomputable section

open EthInapproximability.CurrentPaper

theorem two_pow_clog_le (m : ℕ) : 2 ^ Nat.clog 2 m ≤ 2 * m + 1 := by
  by_cases hm : m ≤ 1
  · rw [Nat.clog_of_right_le_one hm]; omega
  · have h1 : 1 < m := by omega
    have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) h1
    have hpos := Nat.clog_pos (by norm_num : 1 < 2) h1
    have he : 2 ^ Nat.clog 2 m = 2 * 2 ^ (Nat.clog 2 m).pred := by
      have hs : (Nat.clog 2 m).pred + 1 = Nat.clog 2 m := Nat.succ_pred_eq_of_pos hpos
      rw [← pow_succ', hs]
    omega

def W : ℕ := 2 ^ 32 + UnaryBinaryEncoding.coefficient + 6

def seedC : ℕ := 729 * W ^ 6 + 100000

theorem lBd_poly (n : ℕ) : Paper2.LProducer.lBd n ≤ 729 * W ^ 6 * (n + 1) ^ 6 := by
  set V := (n + 3) * W with hVdef
  have hW : 2 ^ 32 ≤ W := by unfold W; omega
  have hW1 : 1 ≤ W := le_trans (Nat.one_le_two_pow) hW
  have hnV : n + 3 ≤ V := by
    rw [hVdef]; exact Nat.le_mul_of_pos_right _ hW1
  have hWV : W ≤ V := by rw [hVdef]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hV : 2 ^ 32 ≤ V := le_trans hW hWV
  have hc : UnaryBinaryEncoding.coefficient + 6 ≤ V := le_trans (by unfold W; omega) hWV
  have hbig : 512 * (2 * n + 3) ≤ V := by
    rw [hVdef]
    have : 512 * (2 * n + 3) ≤ (n + 3) * 2 ^ 32 := by
      have : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
      rw [this]; omega
    exact le_trans this (Nat.mul_le_mul_left _ hW)
  have hLn : Nat.clog 2 n ≤ n := Paper2.FrontClock13.clog_le' n
  have hL : 2 ^ Nat.clog 2 n ≤ V := by
    have := two_pow_clog_le n; omega
  have he : 2 ^ Nat.clog 2 (Nat.clog 2 n + 1) ≤ V := by
    have := two_pow_clog_le (Nat.clog 2 n + 1); omega
  have hee : 2 ^ (Nat.clog 2 (Nat.clog 2 n + 1) * Nat.clog 2 (Nat.clog 2 n + 1)) ≤ V ^ 2 := by
    have hsq := Paper2.FrontClock13.clog_sq_le (Nat.clog 2 n)
    have h1 : 2 ^ (Nat.clog 2 (Nat.clog 2 n + 1) * Nat.clog 2 (Nat.clog 2 n + 1)) ≤
        2 ^ (Nat.clog 2 n + 9) := Nat.pow_le_pow_right (by norm_num) hsq
    have h2 : 2 ^ (Nat.clog 2 n + 9) = 512 * 2 ^ Nat.clog 2 n := by
      rw [pow_add]; ring
    have h3 := two_pow_clog_le n
    have hVV : V ≤ V ^ 2 := by nlinarith
    omega
  have hl := Paper2.FrontClock13.lBd_le n V hV hc hnV hL he hee
  have hV3 : V ≤ 3 * W * (n + 1) := by
    rw [hVdef]; nlinarith
  calc Paper2.LProducer.lBd n ≤ V ^ 6 := hl
    _ ≤ (3 * W * (n + 1)) ^ 6 := Nat.pow_le_pow_left hV3 6
    _ = 729 * W ^ 6 * (n + 1) ^ 6 := by ring

/-- The explicit clock of the seed-table run, as an expression in `n`. -/
def clockExpr (n : ℕ) : ℕ :=
  Paper2.LProducer.lBd n +
    (4 * 2 ^ Paper2.LookupSeed.width (Nat.clog 2 n) + 5 * Paper2.LookupSeed.width (Nat.clog 2 n) + 7) +
    (2 * Paper2.LookupSeed.width (Nat.clog 2 n) + 2) +
    MatrixTableWriter.writerBound (2 ^ Paper2.LookupSeed.width (Nat.clog 2 n))
      (Paper2.LookupSeed.width (Nat.clog 2 n))
      (BitEntry.entryTime (2 ^ Paper2.LookupSeed.width (Nat.clog 2 n))
        (Paper2.LookupSeed.width (Nat.clog 2 n))) + 3

theorem clock_poly (n : ℕ) (hn : 4 ≤ n) : clockExpr n ≤ seedC * (n + 1) ^ 1536 := by
  have hex : clockExpr n = Paper2.LProducer.lBd n +
      (4 * 2 ^ Paper2.LookupSeed.width (Nat.clog 2 n) + 5 * Paper2.LookupSeed.width (Nat.clog 2 n) + 7) +
      (2 * Paper2.LookupSeed.width (Nat.clog 2 n) + 2) +
      MatrixTableWriter.writerBound (2 ^ Paper2.LookupSeed.width (Nat.clog 2 n))
        (Paper2.LookupSeed.width (Nat.clog 2 n))
        (BitEntry.entryTime (2 ^ Paper2.LookupSeed.width (Nat.clog 2 n))
          (Paper2.LookupSeed.width (Nat.clog 2 n))) + 3 := rfl
  have hrs := Paper2.LookupSeed.rows_source_bound n hn
  have hl := lBd_poly n
  have hfin : ((n + 1) ^ 256) ^ 6 = (n + 1) ^ 1536 := by rw [← pow_mul]
  have hN6 : (n + 1) ^ 6 ≤ ((n + 1) ^ 256) ^ 6 := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right (by omega) (by norm_num)
  have hnn : n ^ 256 ≤ (n + 1) ^ 256 := Nat.pow_le_pow_left (by omega) 256
  have hM1 : 1 ≤ (n + 1) ^ 256 := Nat.one_le_pow _ _ (by omega)
  rw [hex, ← hfin]
  clear hex
  generalize Paper2.LookupSeed.width (Nat.clog 2 n) = p at hrs ⊢
  generalize (n + 1) ^ 256 = M at hN6 hnn hM1 ⊢
  generalize Paper2.LProducer.lBd n = lb at hl ⊢
  have hr : 2 ^ p ≤ M := by omega
  have hp : p ≤ M := le_trans (Nat.lt_two_pow_self).le hr
  generalize 2 ^ p = r at hr ⊢
  have hM2 : M ≤ M ^ 2 := by
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ 2 := Nat.pow_le_pow_right hM1 (by norm_num)
  have hT : BitEntry.entryTime r p ≤ 14 * M ^ 2 := by
    unfold BitEntry.entryTime
    have h1 : p * (2 * r + 3) ≤ M * (2 * M + 3) := Nat.mul_le_mul hp (by omega)
    have h2 : M * (2 * M + 3) = 2 * M ^ 2 + 3 * M := by ring
    omega
  have hwb := MatrixTableWriter.writerBound_polynomial r p (BitEntry.entryTime r p)
  have hsum : r + p + BitEntry.entryTime r p + 1 ≤ 17 * M ^ 2 := by omega
  have hcube : (r + p + BitEntry.entryTime r p + 1) ^ 3 ≤ (17 * M ^ 2) ^ 3 :=
    Nat.pow_le_pow_left hsum 3
  have hw : MatrixTableWriter.writerBound r p (BitEntry.entryTime r p) ≤ 98260 * M ^ 6 := by
    have he : 20 * (17 * M ^ 2) ^ 3 = 98260 * M ^ 6 := by ring
    have := Nat.mul_le_mul_left 20 hcube
    omega
  have hl' : lb ≤ 729 * W ^ 6 * M ^ 6 := le_trans hl (Nat.mul_le_mul_left _ hN6)
  have hM6 : M ≤ M ^ 6 := by
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ 6 := Nat.pow_le_pow_right hM1 (by norm_num)
  have h1 : 1 ≤ M ^ 6 := Nat.one_le_pow _ _ hM1
  have hC : seedC * M ^ 6 = 729 * W ^ 6 * M ^ 6 + 100000 * M ^ 6 := by unfold seedC; ring
  rw [hC]
  omega

end

end SeedT45.SeedClock

#print axioms SeedT45.SeedClock.clock_poly
