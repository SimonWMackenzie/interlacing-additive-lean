import CurrentAdditive.TrialLoopCount

/-!
An arithmetic composition for the proposed physical field-list clock.
The constants here are a conservative *budget*. The separate TM2 proofs
must still show that each divisor trial fits the indicated budget and that
seed enumeration/preparation fits the stream budget; this file alone does
not assert a machine run or a runtime theorem.
-/

namespace CurrentAdditive.FiniteFieldConstructor.FieldClockArithmetic

open CurrentAdditive.FiniteFieldMachine.RuntimeArithmetic

def trialBudget (d : ℕ) : ℕ := 100 * (d + 1) ^ 2
def orderedWordBudget (d n : ℕ) : ℕ :=
  n * (d * (4 * d + 5) + 4 * d + 7) + 2
def totalBudget (d n : ℕ) : ℕ :=
  pairCount d * trialBudget d + (2 ^ d) ^ 2 * orderedWordBudget d n

/-- Once the physical per-trial and per-seed run bounds are supplied, their
total has the manuscript's quadratic-in-field-size, quadratic-in-degree
envelope. The theorem is purely arithmetic. -/
theorem totalBudget_le (d n : ℕ) (hd : 0 < d) (hn : 0 < n) :
    totalBudget d n ≤ 120 * (2 ^ d) ^ 2 * n * (d + 1) ^ 2 := by
  have htrials := pairCount_le d hd
  have hunit : d * (4 * d + 5) + 4 * d + 7 ≤ 9 * (d + 1) ^ 2 := by
    nlinarith
  have hword : orderedWordBudget d n ≤ 20 * n * (d + 1) ^ 2 := by
    unfold orderedWordBudget
    have hmul := Nat.mul_le_mul_left n hunit
    have hpos : 1 ≤ n * (d + 1) ^ 2 := by
      have hdn : 1 ≤ (d + 1) ^ 2 := by nlinarith
      nlinarith
    nlinarith
  unfold totalBudget trialBudget
  calc
    pairCount d * (100 * (d + 1) ^ 2) +
        (2 ^ d) ^ 2 * orderedWordBudget d n ≤
      (2 ^ d) ^ 2 * (100 * (d + 1) ^ 2) +
        (2 ^ d) ^ 2 * (20 * n * (d + 1) ^ 2) := by
      gcongr
    _ ≤ 120 * (2 ^ d) ^ 2 * n * (d + 1) ^ 2 := by
      have h100 : 100 * (2 ^ d) ^ 2 * (d + 1) ^ 2 ≤
          100 * (2 ^ d) ^ 2 * n * (d + 1) ^ 2 := by
        calc
          _ = (100 * (2 ^ d) ^ 2 * (d + 1) ^ 2) * 1 := by ring
          _ ≤ (100 * (2 ^ d) ^ 2 * (d + 1) ^ 2) * n :=
            Nat.mul_le_mul_left _ hn
          _ = _ := by ring
      nlinarith [h100]

#print axioms totalBudget_le

end CurrentAdditive.FiniteFieldConstructor.FieldClockArithmetic
