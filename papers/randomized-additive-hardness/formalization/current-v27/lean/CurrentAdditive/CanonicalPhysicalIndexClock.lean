import CurrentAdditive.CanonicalPhysicalIndex

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

def canonicalIndexClock (b t d x y : ℕ) : ℕ :=
  (2 * x + 2) + (8 * x + 3 * ((2 ^ b) ^ (2 ^ (t - 1))) + 4) +
    (2 * y + 2) + (8 * y + 3 * ((2 ^ d) ^ 2) + 4) +
    (8 * (y / ((2 ^ d) ^ 2)) + 3 * (2 ^ b) + 4) + 4

/-- The already checked physical index decoder has a linear clock in
the printed matrix dimensions when the source has a vertex. -/
theorem canonicalIndexClock_linear (v b t d x y : ℕ)
    (hv : 0 < v) (hx : x < rowCount v b t)
    (hy : y < columnCount b t d) :
    canonicalIndexClock b t d x y ≤
      32 * (rowCount v b t + columnCount b t d + 1) := by
  have hsel : (2 ^ b) ^ (2 ^ (t - 1)) ≤ rowCount v b t := by
    unfold rowCount
    have hv1 : 1 ≤ v := hv
    simpa using Nat.mul_le_mul_right ((2 ^ b) ^ (2 ^ (t - 1))) hv1
  have hpay : (2 ^ d) ^ 2 ≤ columnCount b t d := by
    unfold columnCount
    have hq : 1 ≤ 2 ^ (t - 1) * 2 ^ b :=
      Nat.succ_le_of_lt (by positivity)
    calc
      (2 ^ d) ^ 2 = 1 * (2 ^ d) ^ 2 := by ring
      _ ≤ (2 ^ (t - 1) * 2 ^ b) * (2 ^ d) ^ 2 :=
        Nat.mul_le_mul_right _ hq
      _ = _ := by ring
  have hpow : 2 ^ b ≤ columnCount b t d := by
    unfold columnCount
    have hq : 1 ≤ 2 ^ (t - 1) * (2 ^ d) ^ 2 :=
      Nat.succ_le_of_lt (by positivity)
    calc
      2 ^ b = 1 * 2 ^ b := by ring
      _ ≤ (2 ^ (t - 1) * (2 ^ d) ^ 2) * 2 ^ b :=
        Nat.mul_le_mul_right _ hq
      _ = _ := by ring
  have hdiv : y / ((2 ^ d) ^ 2) ≤ y := Nat.div_le_self _ _
  unfold canonicalIndexClock
  omega

#print axioms canonicalIndexClock_linear

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
