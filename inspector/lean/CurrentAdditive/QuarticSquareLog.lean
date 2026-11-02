import CurrentAdditive.QuarticAsymptotics
import Paper2.SquarePadding

namespace CurrentAdditive.QuarticAsymptotics

open Paper2 Paper2.Unit4Shell.Asymptotics
  Paper2.SourceRecursiveNoSampling Paper2.SourceProfileParameters
  CurrentAdditive.RandomizedSchedule

def printedTsq27 (n m Δ : ℕ) (γ : ℚ) (k : ℕ) : ℕ :=
  SquarePadding.entries
    (sourceRows (Nat.clog 2 n)
      (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n))
      (q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ) k)
    (sourceCols (Nat.clog 2 n)
      (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n))
      (q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ) k)

theorem square_log_bounds27 (n m Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hL : 1 ≤ Nat.clog 2 n) :
    Real.logb 2 (printedTsq27 n m Δ γ k) ≤
        Real.logb 2 (printedT27 n m Δ γ k) + 3 +
          Real.logb 2 (Nat.clog 2 n) ∧
      2 ^ k ≤ printedTsq27 n m Δ γ k := by
  set L := Nat.clog 2 n
  set r := 4 * RestorationWidthScheduleScratch.ell L
  set q := q27 (V := Fin n) (E := Fin m) L γ Δ
  have hlt := ReductionDimensions.square_entries_lt
    (compressionEntropy (sourceRank L r q k) (sourceCost L r q k)) L hL
  have hlt' : printedTsq27 n m Δ γ k <
      8 * L * printedT27 n m Δ γ k := by
    simpa [printedTsq27, printedT27, ReductionDimensions.entries,
      sourceRows, sourceCols, L, r, q] using hlt
  have hlow := two_pow_le_entries L r q k hL
  have hT1 : 1 ≤ printedT27 n m Δ γ k :=
    le_trans Nat.one_le_two_pow hlow
  have hsq : 2 ^ k ≤ printedTsq27 n m Δ γ k := by
    have hcol := SquarePadding.cols_le_side
      (sourceRows L r q k) (sourceCols L r q k)
    have hside := SquarePadding.side_pos
      (sourceRows L r q k) (sourceCols L r q k)
    have hc : 2 ^ k ≤ sourceCols L r q k := by
      have hH : k ≤ sourceCost L r q k - 1 := by
        unfold sourceCost
        have h1 : k ≤ k * (SourceProfileParameters.exponent L +
            SourceProfileParameters.outerExponent L + SourceProfileParameters.exponent L +
            r + q + 1) := Nat.le_mul_of_pos_right k (Nat.succ_pos _)
        omega
      have hpow : 2 ^ k ≤ 2 ^ (sourceCost L r q k - 1) :=
        Nat.pow_le_pow_right (by decide) hH
      have hE : 2 ^ (sourceCost L r q k - 1) ≤
          compressionEntropy (sourceRank L r q k) (sourceCost L r q k) := by
        unfold compressionEntropy
        exact Nat.le_mul_of_pos_left _ (by omega)
      have hcol' : compressionEntropy (sourceRank L r q k) (sourceCost L r q k) ≤
          sourceCols L r q k := by
        unfold sourceCols compressionColumnDraws
        omega
      exact hpow.trans (hE.trans hcol')
    unfold printedTsq27 SquarePadding.entries
    calc
      2 ^ k ≤ sourceCols L r q k := hc
      _ ≤ SquarePadding.side (sourceRows L r q k) (sourceCols L r q k) := hcol
      _ ≤ _ := Nat.le_mul_of_pos_left _ hside
  refine ⟨?_, hsq⟩
  have hTsqpos : (0 : ℝ) < printedTsq27 n m Δ γ k := by
    have : 0 < printedTsq27 n m Δ γ k :=
      lt_of_lt_of_le Nat.one_le_two_pow hsq
    exact_mod_cast this
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hTR : (0 : ℝ) < printedT27 n m Δ γ k := by exact_mod_cast hT1
  have hle : (printedTsq27 n m Δ γ k : ℝ) ≤
      8 * L * printedT27 n m Δ γ k := by exact_mod_cast hlt'.le
  have := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
    hTsqpos (by positivity)).mpr hle
  rw [Real.logb_mul (by positivity) hTR.ne',
    Real.logb_mul (by norm_num) hLR.ne'] at this
  have h8 : Real.logb 2 (8 : ℝ) = 3 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  rw [h8] at this
  dsimp [L] at this
  linarith

#print axioms square_log_bounds27

end CurrentAdditive.QuarticAsymptotics
