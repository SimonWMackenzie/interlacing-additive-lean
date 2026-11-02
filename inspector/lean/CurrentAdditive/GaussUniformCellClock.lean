import CurrentAdditive.GaussUniformCellAlgebra
import CurrentAdditive.GaussSourceCellClock

/-! Uniform byte cap for the adapted physical Gauss cell request. -/

namespace CurrentAdditive.GaussUniformCellClock

open CurrentAdditive.CodeDCodec
open CurrentAdditive.GaussPhysical

theorem adapted_packet_length (flag : Bool)
    (current column row pivot : RawRat) (S : Nat) (hS : 1 ≤ S)
    (hcurrent : (encodeRawRat current).length ≤ 4*S+5)
    (hcolumn : (encodeRawRat column).length ≤ 4*S+5)
    (hrow : (encodeRawRat row).length ≤ 4*S+5)
    (hpivot : (encodeRawRat pivot).length ≤ 4*S+5) :
    (GaussUniformCellAlgebra.adaptedPacket
      flag current column row pivot).length ≤ 32*S+54 := by
  cases flag with
  | false =>
      simpa [GaussUniformCellAlgebra.adaptedPacket,
        GaussUniformCellAlgebra.adaptedCurrent,
        GaussUniformCellAlgebra.adaptedColumn] using
        (cellPacket_length false current column row pivot S
          hcurrent hcolumn hrow hpivot)
  | true =>
      have hzero : (encodeRawRat (rawOfRat 0)).length ≤ 4*S+5 := by
        apply rawOfRat_code_length 0 S <;> norm_num <;> omega
      have hminus : (encodeRawRat (rawOfRat (-1))).length ≤ 4*S+5 := by
        apply rawOfRat_code_length (-1) S <;> norm_num <;> omega
      simpa [GaussUniformCellAlgebra.adaptedPacket,
        GaussUniformCellAlgebra.adaptedCurrent,
        GaussUniformCellAlgebra.adaptedColumn] using
        (cellPacket_length false (rawOfRat 0) (rawOfRat (-1))
          row pivot S hzero hminus hrow hpivot)

theorem actual_adapted_source_packet_length {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (t : Nat) (ht : t ≤ k)
    (r pivot i : Fin m) (c j : Fin k) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let B := (CurrentAdditive.EliminationEntryBounds.cursorAfter Aq t).B
    (GaussUniformCellAlgebra.adaptedSourceCellPacket B r pivot c i j).length ≤
      32*((m+3)*(m+1)^2+1)+54 := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let B := (CurrentAdditive.EliminationEntryBounds.cursorAfter Aq t).B
  let S := (m+3)*(m+1)^2+1
  have hS : 1 ≤ S := by omega
  have hentry (u : Fin m) (v : Fin k) :
      (encodeRawRat (rawOfRat (B u v))).length ≤ 4*S+5 :=
    actualGauss_cell_code_length A h01 t ht u v
  exact adapted_packet_length (decide (i=r))
    (rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot i) j))
    (rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot i) c))
    (rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot r) j))
    (rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot r) c))
    S hS (hentry _ _) (hentry _ _) (hentry _ _) (hentry _ _)

#print axioms adapted_packet_length
#print axioms actual_adapted_source_packet_length

end CurrentAdditive.GaussUniformCellClock
