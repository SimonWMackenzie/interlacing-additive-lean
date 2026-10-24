import CurrentAdditive.RationalArrayUpdate

namespace CurrentAdditive.RationalCandidateCompletion

open CurrentAdditive.RationalBitBounds

/-- The squared Gram common denominator pays four copies of the row count
in the exponent. Thus each selected coefficient has O(m log(m+1)) bits. -/
theorem shared_gram_pow_bound (m : Nat) :
    (m.factorial * m ^ m) ^ 2 ≤ (m + 1) ^ (4 * m) := by
  have hf : m.factorial ≤ m ^ m := Nat.factorial_le_pow m
  have hpow : m ^ m ≤ (m + 1) ^ m :=
    Nat.pow_le_pow_left (by omega) _
  calc
    (m.factorial * m ^ m) ^ 2 ≤
        ((m + 1) ^ m * (m + 1) ^ m) ^ 2 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul (hf.trans hpow) hpow) _
    _ = (m + 1) ^ (4 * m) := by
      rw [← pow_add, ← pow_mul]
      congr 1
      omega

theorem shared_gram_bits (m z : Nat)
    (hz : z ≤ (m.factorial * m ^ m) ^ 2) :
    Nat.size z ≤ 4 * m * Nat.size (m + 1) + 1 := by
  have hbase : m + 1 ≤ 2 ^ Nat.size (m + 1) :=
    le_of_lt (Nat.lt_size_self _)
  have hbound : z ≤ 2 ^ (4 * m * Nat.size (m + 1)) := by
    calc
      z ≤ (m.factorial * m ^ m) ^ 2 := hz
      _ ≤ (m + 1) ^ (4 * m) := shared_gram_pow_bound m
      _ ≤ (2 ^ Nat.size (m + 1)) ^ (4 * m) :=
        Nat.pow_le_pow_left hbase _
      _ = 2 ^ (4 * m * Nat.size (m + 1)) := by
        simp only [← pow_mul]
        congr 1
        ring
  exact size_le_of_pow_bound hbound

#print axioms shared_gram_pow_bound
#print axioms shared_gram_bits

end CurrentAdditive.RationalCandidateCompletion
