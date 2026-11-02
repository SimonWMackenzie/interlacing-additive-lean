import CurrentAdditive.DivisionStep

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

theorem lt_pow_of_topBit_false {n k : ℕ}
    (hn : n < 2 ^ (k + 1)) (hbit : n.testBit k = false) :
    n < 2 ^ k := by
  apply Nat.lt_of_testBit k hbit
  · simp [Nat.testBit_two_pow]
  · intro j hj
    have hpow : 2 ^ (k + 1) ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_eq_false_of_lt (hn.trans_le hpow)]
    simp only [Nat.testBit_two_pow]
    simp [ne_of_lt hj]

theorem monicBits_shifted_topBit (e i tail : ℕ) (htail : tail < 2 ^ e) :
    ((TrialSearch.monicBits e tail) <<< i).testBit (e + i) = true := by
  rw [Nat.testBit_shiftLeft]
  simpa [show i ≤ e + i by omega, Nat.add_sub_cancel_right] using
    monicBits_topBit e tail htail

theorem divisionStep_topBit_false (e i divisor acc : ℕ)
    (hdivbit : (divisor <<< i).testBit (e + i) = true) :
    (if acc.testBit (e + i) then Nat.xor acc (divisor <<< i) else acc).testBit
      (e + i) = false := by
  by_cases haccbit : acc.testBit (e + i)
  · simp [haccbit, Nat.testBit_xor, hdivbit]
  · simp [haccbit]

theorem divisionStep_drop (e i divisor acc : ℕ)
    (hdivisor : divisor < 2 ^ (e + 1))
    (hdivbit : (divisor <<< i).testBit (e + i) = true)
    (hacc : acc < 2 ^ (e + i + 1)) :
    (if acc.testBit (e + i) then Nat.xor acc (divisor <<< i) else acc) <
      2 ^ (e + i) := by
  apply lt_pow_of_topBit_false
  · exact divisionStep_lt (e + i) e i divisor acc (le_refl _)
      hdivisor (by simpa [Nat.add_assoc] using hacc)
  · exact divisionStep_topBit_false e i divisor acc hdivbit

#print axioms divisionStep_drop

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
