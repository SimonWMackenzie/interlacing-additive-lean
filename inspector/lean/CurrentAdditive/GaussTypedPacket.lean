import CurrentAdditive.GaussPacket

namespace CurrentAdditive.GaussPhysical

open CurrentAdditive.CodeDCodec

def typedRows {m k : ℕ} (B : Fin m → Fin k → ℚ) : List (List ℚ) :=
  (List.finRange m).map (fun i => (List.finRange k).map (B i))

theorem typedRows_length {m k : ℕ} (B : Fin m → Fin k → ℚ) :
    (typedRows B).length = m := by simp [typedRows]

theorem typedRows_row_length {m k : ℕ} (B : Fin m → Fin k → ℚ)
    (row : List ℚ) (hrow : row ∈ typedRows B) :
    row.length = k := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hrow
  simp

def encodeTypedMatrix {m k : ℕ} (B : Fin m → Fin k → ℚ) :
    List Bool :=
  encodeRationalMatrix (typedRows B)

theorem decodeTypedMatrix {m k : ℕ} (B : Fin m → Fin k → ℚ) :
    (decodeMatrix (encodeTypedMatrix B)).map matrixValues =
      some (typedRows B) :=
  decodeRationalMatrix (typedRows B)

/-- The precise rational matrix returned by the materialized pivot loop is
encoded in the shared nested-row packet format. This theorem is semantic;
the physical writer is an independent machine obligation. -/
theorem decodeMaterializedPrefix {m k : ℕ}
    (A : Fin m → Fin k → ℚ) (fuel : ℕ) :
    (decodeMatrix (encodeTypedMatrix
      (CurrentAdditive.MaterializedGauss.echelonMaterialized
        A 0 0 fuel).1)).map matrixValues =
      some (typedRows
        (CurrentAdditive.MaterializedGauss.echelonMaterialized
          A 0 0 fuel).1) :=
  decodeTypedMatrix _

end CurrentAdditive.GaussPhysical
