import CurrentAdditive.DivisionBitDrop

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

def step (e i divisor acc : ℕ) : ℕ :=
  if acc.testBit (e + i) then Nat.xor acc (divisor <<< i) else acc

def run (e divisor : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | m + 1, acc => run e divisor m (step e m divisor acc)

theorem reverse_range_succ (m : ℕ) :
    (List.range (m + 1)).reverse = m :: (List.range m).reverse := by
  simp [List.range_succ]

theorem run_eq_fold (e divisor m acc : ℕ) :
    run e divisor m acc =
      (List.range m).reverse.foldl (fun a i => step e i divisor a) acc := by
  induction m generalizing acc with
  | zero => rfl
  | succ m ih =>
      rw [run, reverse_range_succ]
      simpa [List.foldl_cons] using ih (step e m divisor acc)

theorem remainder_eq_run (d e divisor dividend : ℕ) :
    TrialSearch.remainder d e divisor dividend =
      run e divisor (d - e + 1) dividend := by
  exact (run_eq_fold e divisor (d - e + 1) dividend).symm

theorem run_lt (e divisor m acc : ℕ)
    (hdivisor : divisor < 2 ^ (e + 1))
    (htop : divisor.testBit e = true)
    (hacc : acc < 2 ^ (e + m)) :
    run e divisor m acc < 2 ^ e := by
  induction m generalizing acc with
  | zero => simpa [run] using hacc
  | succ m ih =>
      rw [run]
      apply ih
      change step e m divisor acc < 2 ^ (e + m)
      apply divisionStep_drop e m divisor acc hdivisor
      · rw [Nat.testBit_shiftLeft]
        simpa [show m ≤ e + m by omega, Nat.add_sub_cancel_right] using htop
      · simpa [Nat.add_assoc] using hacc

theorem remainder_lt (d e tailDivisor tailDividend : ℕ)
    (he : e ≤ d) (hdivisor : tailDivisor < 2 ^ e)
    (hdividend : tailDividend < 2 ^ d) :
    TrialSearch.remainder d e (TrialSearch.monicBits e tailDivisor)
      (TrialSearch.monicBits d tailDividend) < 2 ^ e := by
  rw [remainder_eq_run]
  apply run_lt
  · exact monicBits_lt e tailDivisor hdivisor
  · exact monicBits_topBit e tailDivisor hdivisor
  · have h := monicBits_lt d tailDividend hdividend
    have heq : e + (d - e + 1) = d + 1 := by omega
    rw [heq]
    exact h

#print axioms remainder_lt

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
