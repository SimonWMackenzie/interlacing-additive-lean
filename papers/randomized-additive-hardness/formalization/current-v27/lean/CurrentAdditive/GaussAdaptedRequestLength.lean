import CurrentAdditive.GaussUniformMatrixGlobal

/-! Size of the complete physically serialized m-by-k request list. -/

namespace CurrentAdditive.GaussAdaptedRequestLength

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussNestedMatrixMap

theorem encoded_adapted_length_le {m k : Nat}
    (B : Fin m → Fin k → ℚ) (r pivot : Fin m) (c : Fin k)
    (L : Nat)
    (hcell : ∀ i j,
      (GaussUniformCellAlgebra.adaptedSourceCellPacket
        B r pivot c i j).length ≤ L) :
    (encodeNested (GaussAdaptedMatrixMap.adaptedMatrix B r pivot c)).length ≤
      listBytes m (listBytes k L) := by
  let rows := GaussAdaptedMatrixMap.adaptedMatrix B r pivot c
  have hrow (row : List (List Bool)) (hr : row ∈ rows) :
      (SourceListEncoding.encode row).length ≤ listBytes k L := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
    have h := SourceListEncoding.encode_map_length_le
      (List.finRange k)
      (GaussUniformCellAlgebra.adaptedSourceCellPacket B r pivot c i)
      L (by intro j hj; exact hcell i j)
    simpa [listBytes] using h
  have houter := SourceListEncoding.encode_map_length_le
    rows SourceListEncoding.encode (listBytes k L) hrow
  simpa [encodeNested, rows, GaussAdaptedMatrixMap.adaptedMatrix,
    listBytes] using houter

theorem actual_encoded_adapted_length_le {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (t : Nat) (ht : t ≤ k)
    (r pivot : Fin m) (c : Fin k) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let B := (CurrentAdditive.GaussControlTrace.after Aq t).B
    (encodeNested (GaussAdaptedMatrixMap.adaptedMatrix B r pivot c)).length ≤
      listBytes m (listBytes k (GaussUniformMatrixActual.requestCap m)) := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let B := (CurrentAdditive.GaussControlTrace.after Aq t).B
  have hB := congrArg CurrentAdditive.EliminationEntryBounds.CursorState.B
    (CurrentAdditive.GaussControlTrace.after_cursor Aq t)
  change B = (CurrentAdditive.EliminationEntryBounds.cursorAfter Aq t).B at hB
  apply encoded_adapted_length_le B r pivot c
    (GaussUniformMatrixActual.requestCap m)
  intro i j
  rw [hB]
  simpa only [GaussUniformMatrixActual.requestCap,
    GaussUniformMatrixActual.entryCap, Aq] using
    (GaussUniformCellClock.actual_adapted_source_packet_length
      A h01 t ht r pivot i c j)

#print axioms encoded_adapted_length_le
#print axioms actual_encoded_adapted_length_le

end CurrentAdditive.GaussAdaptedRequestLength
