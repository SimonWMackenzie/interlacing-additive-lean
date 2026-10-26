import CurrentAdditive.GaussPacket

namespace CurrentAdditive.GaussPhysical

open CurrentAdditive.CodeDCodec
open EthInapproximability.CurrentPaper

/-- The fixed three-bank representation of a canonical rational cell is
linear in the binary lengths of its canonical numerator and denominator. -/
theorem rawOfRat_code_length (q : ℚ) (S : ℕ)
    (hn : Nat.size q.num.natAbs ≤ S)
    (hd : Nat.size q.den ≤ S) :
    (encodeRawRat (rawOfRat q)).length ≤ 4 * S + 5 := by
  rw [encodeRawRat, BitMachineBankCodec.encode_length]
  have hs : (if q < 0 then [true] else ([] : List Bool)).length ≤ 1 := by
    split_ifs <;> simp
  simp [rawRatBank, rawOfRat, Fin.sum_univ_succ, Nat.size_eq_bits_len] at *
  omega

theorem actualGauss_cell_code_length {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (t : ℕ) (ht : t ≤ k) (i : Fin m) (j : Fin k) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let q := (CurrentAdditive.EliminationEntryBounds.cursorAfter Aq t).B i j
    (encodeRawRat (rawOfRat q)).length ≤
      4 * ((m + 3) * (m + 1) ^ 2 + 1) + 5 := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let q := (CurrentAdditive.EliminationEntryBounds.cursorAfter Aq t).B i j
  have hh := CurrentAdditive.EliminationEntryBounds.every_actual_step_entry_bits
    A h01 t ht i j
  exact rawOfRat_code_length q _ hh.2 hh.1

end CurrentAdditive.GaussPhysical
