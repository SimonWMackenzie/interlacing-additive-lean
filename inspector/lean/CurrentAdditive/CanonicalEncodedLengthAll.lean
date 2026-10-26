import CurrentAdditive.CanonicalEncodedLength

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open CurrentAdditive.SmallBias
open EthInapproximability.CurrentPaper.EncodedCommunication

theorem encoded_table_length_general {r c : ℕ}
    (T : Paper2.YaoMaterialization.SerializedTable r c)
    (budget : ℕ) :
    (encodeInstance (Paper2.EncodedSelectedOutput.instanceOf T budget)).length ≤
      2 * (r + c + budget) + 3 + T.bits.length := by
  have hrbits : r.bits.length ≤ r := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hcbits : c.bits.length ≤ c := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hbbits : budget.bits.length ≤ budget := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  rw [encodeInstance_length]
  simp only [Paper2.EncodedSelectedOutput.instanceOf] at *
  omega

/-- The same encoded output-size polynomial covers zero-vertex decoded
codes, which the total `renderClone` function must handle. -/
theorem encoded_instance_length_polynomial_all {v e : ℕ} (b t : ℕ)
    (ht : 4 ≤ t) (modulus : ℕ) (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) :
    (encodeInstance (instanceOfTable b t (publicFieldDegree b t)
      modulus he edges)).length ≤
      5 * tableConstant t * (v + 1) * (2 ^ b) ^ tableExponent t +
        2 * (2 * b + 4 * t + 2) + 3 := by
  let r := rowCount v b t
  let r1 := rowCount (v + 1) b t
  let c := columnCount b t (publicFieldDegree b t)
  let P := tableConstant t * (v + 1) * (2 ^ b) ^ tableExponent t
  have hc : 0 < c := by dsimp [c, columnCount]; positivity
  have hr1 : 0 < r1 := by dsimp [r1, rowCount]; positivity
  have hrle : r ≤ r1 := by
    dsimp [r, r1, rowCount]
    exact Nat.mul_le_mul_right _ (Nat.le_succ v)
  have hrP : r1 ≤ P := by
    have h := table_entry_count_polynomial (v + 1) b t ht
    have hrc : r1 ≤ r1 * c := by
      simpa using Nat.mul_le_mul_left r1 hc
    exact hrc.trans h
  have hcP : c ≤ P := by
    have h := table_entry_count_polynomial (v + 1) b t ht
    have hcr : c ≤ r1 * c := by
      simpa using Nat.mul_le_mul_right c hr1
    exact hcr.trans h
  have hbits :
      (table b t (publicFieldDegree b t) modulus he edges).bits.length ≤ P := by
    have h := table_bits_polynomial b t ht modulus he edges
    have hmul : tableConstant t * v * (2 ^ b) ^ tableExponent t ≤ P := by
      dsimp [P]
      gcongr
      omega
    exact h.trans hmul
  have hlen := encoded_table_length_general
    (table b t (publicFieldDegree b t) modulus he edges)
    (2 * b + 4 * t + 2)
  unfold instanceOfTable
  have hsum : r + c + (2 * b + 4 * t + 2) ≤
      2 * P + (2 * b + 4 * t + 2) := by omega
  have hle : (encodeInstance (Paper2.EncodedSelectedOutput.instanceOf
      (table b t (publicFieldDegree b t) modulus he edges)
      (2 * b + 4 * t + 2))).length ≤
      5 * P + 2 * (2 * b + 4 * t + 2) + 3 := by omega
  simpa only [P, mul_assoc] using hle

#print axioms encoded_table_length_general
#print axioms encoded_instance_length_polynomial_all

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
