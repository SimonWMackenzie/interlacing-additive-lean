import Paper2.LMain
import Paper2.ParameterizedCanonicalSource

/-! Unit 3, segment (2), first part: the outputs of `LProducer.lProg` are the literal scheduled raw
public counts `p = LookupSeed.width L`, `s = width L`, `q₁ = width L - 2`, `q₂ = outerWidth L`,
`w = ParameterizedCanonicalSource.restorationWidth L` at `L = clog₂ n` (definitions read literally:
`LookupSeed.exponent L = clog₂ (64 (L+1))`, `SourceProfileParameters.exponent L = clog₂ (65536 (L+1))`,
`outerExponent L = L + 2 exponent L`, `RestorationWidthScheduleScratch.width L = 2 ^ (clog₂ (L+1)) ^ 2`). -/

set_option maxRecDepth 16384

namespace Paper2.LProducer

theorem clog_two_mul (y : ℕ) (hy : 1 ≤ y) : Nat.clog 2 (2 * y) = Nat.clog 2 y + 1 := by
  rw [Nat.clog_of_two_le (by norm_num) (by omega)]
  congr 1
  congr 1
  omega

theorem clog_two_pow_mul (k y : ℕ) (hy : 1 ≤ y) : Nat.clog 2 (2 ^ k * y) = k + Nat.clog 2 y := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc, clog_two_mul _ (Nat.mul_pos (Nat.two_pow_pos k) hy), ih]
      omega

theorem p_eq (L : ℕ) : LookupSeed.width L = 2 ^ (6 + Nat.clog 2 (L + 1)) := by
  unfold LookupSeed.width LookupSeed.exponent
  rw [show 64 * (L + 1) = 2 ^ 6 * (L + 1) by norm_num, clog_two_pow_mul 6 _ (by omega)]

theorem s_eq (L : ℕ) : SourceProfileParameters.width L = 2 ^ (16 + Nat.clog 2 (L + 1)) := by
  unfold SourceProfileParameters.width SourceProfileParameters.exponent
  rw [show 65536 * (L + 1) = 2 ^ 16 * (L + 1) by norm_num, clog_two_pow_mul 16 _ (by omega)]

theorem q₂_eq (L : ℕ) : SourceProfileParameters.outerWidth L =
    2 ^ (32 + (Nat.clog 2 (L + 1) + (Nat.clog 2 (L + 1) + L))) := by
  unfold SourceProfileParameters.outerWidth SourceProfileParameters.outerExponent
    SourceProfileParameters.exponent
  rw [show 65536 * (L + 1) = 2 ^ 16 * (L + 1) by norm_num, clog_two_pow_mul 16 _ (by omega)]
  congr 1
  omega

theorem w_eq (L : ℕ) : ParameterizedCanonicalSource.restorationWidth L =
    2 ^ (Nat.clog 2 (L + 1) * Nat.clog 2 (L + 1)) := by
  unfold ParameterizedCanonicalSource.restorationWidth RestorationWidthScheduleScratch.width
    RestorationWidthScheduleScratch.depth RestorationWidthScheduleScratch.ell
  rw [sq]

/-- Segment (2), first part: the `L`-determined raw public counts are PRODUCED from unary `n` by the
ONE fixed program `lProg`, each in its own cell, at the literal scheduled values. -/
theorem l_run_sched (n : ℕ) :
    let L := Nat.clog 2 n
    ∃ t ≤ lBd n, ∃ vc, ∃ F : LK → List Bool,
      ((EthInapproximability.CurrentPaper.BitMachineEncoding.advance lProg)^[t])
          (⟨some lStart, lCtl, L0 n⟩ : Turing.TM2.Cfg (fun _ : LK => Bool) _ _) = ⟨none, vc, F⟩ ∧
      F nC = u n ∧ F pC = u (LookupSeed.width L) ∧ F sC = u (SourceProfileParameters.width L) ∧
      F q1C = u (SourceProfileParameters.width L - 2) ∧
      F q2C = u (SourceProfileParameters.outerWidth L) ∧
      F wC = u (ParameterizedCanonicalSource.restorationWidth L) := by
  intro L
  obtain ⟨t, ht, vc, F, hr, h0, -, -, -, -, -, -, hp, hs, hq2, hw, hq1, -⟩ := l_run n
  refine ⟨t, ht, vc, F, hr, h0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp, p_eq]
  · rw [hs, s_eq]
  · rw [hq1, s_eq]
  · rw [hq2, q₂_eq]
  · rw [hw, w_eq]

#print axioms clog_two_pow_mul
#print axioms p_eq
#print axioms s_eq
#print axioms q₂_eq
#print axioms w_eq
#print axioms l_run_sched

end Paper2.LProducer
