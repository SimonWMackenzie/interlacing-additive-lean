import CurrentAdditive.Negate

/-! The physical sign-change machine preserves the exact canonical RawRat
representation expected by the Gauss vector packet. -/

namespace CurrentAdditive.GaussRationalNegateCanonical

open CurrentAdditive.GaussCertificateNegate
open CurrentAdditive.GaussPhysical

theorem negateRaw_rawOfRat (q : ℚ) :
    negateRaw (rawOfRat q) = rawOfRat (-q) := by
  unfold negateRaw rawOfRat
  simp only [Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den, Int.natAbs_neg]
  by_cases hz : q.num = 0
  · have hq : q = 0 := Rat.num_eq_zero.mp hz
    simp [hq]
  · by_cases hn : q.num < 0
    · have hb : q.num.natAbs.bits ≠ [] := by
        intro he
        have hs : q.num.natAbs.size = 0 := by
          rw [← Nat.size_eq_bits_len]
          simpa using congrArg List.length he
        exact hz (Int.natAbs_eq_zero.mp (Nat.size_eq_zero.mp hs))
      have hq : q < 0 := Rat.num_neg.mp hn
      simp [hb, hn, Rat.num_pos]
      exact le_of_lt hq
    · have hb : q.num.natAbs.bits ≠ [] := by
        intro he
        have hs : q.num.natAbs.size = 0 := by
          rw [← Nat.size_eq_bits_len]
          simpa using congrArg List.length he
        exact hz (Int.natAbs_eq_zero.mp (Nat.size_eq_zero.mp hs))
      have hpos : 0 < q.num := by omega
      have hq : 0 < q := Rat.num_pos.mp hpos
      simp [hb, hq, hn, Rat.num_pos]

theorem result_canonical (q : ℚ) :
    result (CurrentAdditive.CodeDCodec.encodeRawRat (rawOfRat q)) =
      CurrentAdditive.CodeDCodec.encodeRawRat (rawOfRat (-q)) := by
  rw [result_raw, negateRaw_rawOfRat]

theorem outputs_canonical (q : ℚ) :
    machine.OutputsWithin
      (CurrentAdditive.CodeDCodec.encodeRawRat (rawOfRat q))
      (CurrentAdditive.CodeDCodec.encodeRawRat (rawOfRat (-q)))
      (7 * ((CurrentAdditive.CodeDCodec.encodeRawRat (rawOfRat q)).length + 1) +
        2 + 2 * ((CurrentAdditive.CodeDCodec.encodeRawRat (rawOfRat q)).length + 2) + 4) := by
  simpa [result_canonical] using
    (outputs (CurrentAdditive.CodeDCodec.encodeRawRat (rawOfRat q)))

#print axioms outputs_canonical

end CurrentAdditive.GaussRationalNegateCanonical
