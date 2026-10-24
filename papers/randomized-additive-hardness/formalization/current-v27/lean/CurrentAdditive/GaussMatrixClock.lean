import CurrentAdditive.GaussCellClock

namespace CurrentAdditive.GaussPhysical

open CurrentAdditive.CodeDCodec
open EthInapproximability.CurrentPaper

/-- A rectangular rational matrix with uniformly short canonical entries
has a short nested SourceListEncoding packet. -/
theorem encodeTypedMatrix_length {m k : ℕ}
    (B : Fin m → Fin k → ℚ) (S : ℕ)
    (hbits : ∀ i j,
      Nat.size (B i j).num.natAbs ≤ S ∧ Nat.size (B i j).den ≤ S) :
    (encodeTypedMatrix B).length ≤
      3 * m * (3 * k * (4 * S + 6) + 2) + 1 := by
  have hcell (i : Fin m) (j : Fin k) :
      (encodeRawRat (rawOfRat (B i j))).length ≤ 4 * S + 5 :=
    rawOfRat_code_length (B i j) S (hbits i j).1 (hbits i j).2
  have hrow (i : Fin m) :
      (encodeRow ((List.finRange k).map (rawOfRat ∘ B i))).length ≤
        3 * k * (4 * S + 6) + 1 := by
    have h := SourceListEncoding.encode_map_length_le
      (List.finRange k) (fun j => encodeRawRat (rawOfRat (B i j)))
      (4 * S + 5) (by
        intro j hj
        exact hcell i j)
    simpa [encodeRow, CurrentAdditive.CodeDCodecV2.encodeItems,
      List.map_map, Function.comp_def] using h
  have houter := SourceListEncoding.encode_map_length_le
    (List.finRange m)
    (fun i => encodeRow ((List.finRange k).map (rawOfRat ∘ B i)))
    (3 * k * (4 * S + 6) + 1) (by
      intro i hi
      exact hrow i)
  simpa [encodeTypedMatrix, encodeRationalMatrix, encodeMatrix,
    typedRows, CurrentAdditive.CodeDCodecV2.encodeItems,
    List.map_map, Function.comp_def] using houter

/-- The complete encoded actual matrix at every recursive Gauss call has
a polynomial size bound in its row and column counts. -/
theorem actualGauss_matrix_packet_length {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (t : ℕ) (ht : t ≤ k) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let B := (CurrentAdditive.EliminationEntryBounds.cursorAfter Aq t).B
    (encodeTypedMatrix B).length ≤
      3 * m * (3 * k *
        (4 * ((m + 3) * (m + 1) ^ 2 + 1) + 6) + 2) + 1 := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let B := (CurrentAdditive.EliminationEntryBounds.cursorAfter Aq t).B
  apply encodeTypedMatrix_length B _
  intro i j
  have h := CurrentAdditive.EliminationEntryBounds.every_actual_step_entry_bits
    A h01 t ht i j
  exact ⟨h.2, h.1⟩

end CurrentAdditive.GaussPhysical
