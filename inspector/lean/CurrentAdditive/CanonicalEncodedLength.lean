import CurrentAdditive.CanonicalTableBounds
import EthInapproximability.CurrentPaper.EncodedCommunication

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open CurrentAdditive.SmallBias
open EthInapproximability.CurrentPaper.EncodedCommunication

/-- The three length fields add only linear overhead to a nonempty table. -/
theorem encoded_table_length_le {r c : ℕ}
    (T : Paper2.YaoMaterialization.SerializedTable r c)
    (budget : ℕ) (hr : 0 < r) (hc : 0 < c) :
    (encodeInstance (Paper2.EncodedSelectedOutput.instanceOf T budget)).length ≤
      5 * T.bits.length + 2 * budget + 3 := by
  have hrow : r ≤ T.bits.length := by
    rw [T.length]
    simpa using Nat.mul_le_mul_left r hc
  have hcol : c ≤ T.bits.length := by
    rw [T.length]
    simpa using Nat.mul_le_mul_right c hr
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

/-- Explicit bit-length bound for the actual encoded canonical instance. -/
theorem encoded_instance_length_polynomial {v e : ℕ} (b t : ℕ)
    (ht : 4 ≤ t) (hv : 0 < v) (modulus : ℕ)
    (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) :
    (encodeInstance (instanceOfTable b t (publicFieldDegree b t)
      modulus he edges)).length ≤
      5 * tableConstant t * v * (2 ^ b) ^ tableExponent t +
        2 * (2 * b + 4 * t + 2) + 3 := by
  have hrow : 0 < rowCount v b t := by
    unfold rowCount
    positivity
  have hcol : 0 < columnCount b t (publicFieldDegree b t) := by
    unfold columnCount
    positivity
  have hcore := encoded_table_length_le
    (table b t (publicFieldDegree b t) modulus he edges)
    (2 * b + 4 * t + 2) hrow hcol
  have htable := table_bits_polynomial b t ht modulus he edges
  have hscaled := Nat.mul_le_mul_left 5 htable
  unfold instanceOfTable
  calc
    _ ≤ 5 * (table b t (publicFieldDegree b t) modulus he edges).bits.length +
          2 * (2 * b + 4 * t + 2) + 3 := hcore
    _ ≤ 5 * (tableConstant t * v * (2 ^ b) ^ tableExponent t) +
          2 * (2 * b + 4 * t + 2) + 3 := by omega
    _ = _ := by ring

#print axioms encoded_table_length_le
#print axioms encoded_instance_length_polynomial

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
