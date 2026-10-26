import CurrentAdditive.GaussAdaptedPacketCompat64
import CurrentAdditive.GaussUniformCellAlgebra

namespace CurrentAdditive.GaussAdaptedNamedBridge64

open CurrentAdditive.CodeDCodec
open Turing Turing.TM2

theorem packet_named (flag : Bool) (current column row pivot : RawRat) :
    GaussAdaptedPacket64.packet flag (encodeRawRat current)
      (encodeRawRat column) (encodeRawRat row) (encodeRawRat pivot) =
    GaussUniformCellAlgebra.adaptedPacket flag current column row pivot := by
  rw [GaussAdaptedPacket64.packet_eq_sourceAdaptedPacket]
  rfl

theorem source_cell_named {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (i : Fin m) (j : Fin k) :
    GaussAdaptedPacket64.packet (decide (i = r))
      (encodeRawRat (GaussPhysical.rawOfRat
        (B (GaussCellSourceBridge.sourceRow r pivot i) j)))
      (encodeRawRat (GaussPhysical.rawOfRat
        (B (GaussCellSourceBridge.sourceRow r pivot i) c)))
      (encodeRawRat (GaussPhysical.rawOfRat
        (B (GaussCellSourceBridge.sourceRow r pivot r) j)))
      (encodeRawRat (GaussPhysical.rawOfRat
        (B (GaussCellSourceBridge.sourceRow r pivot r) c))) =
    GaussUniformCellAlgebra.adaptedSourceCellPacket B r pivot c i j := by
  rw [packet_named]
  rfl

theorem output_source_cell_named {m k : Nat} (B : Fin m → Fin k → ℚ)
    (S : Fin 64 → List Bool) (r pivot : Fin m) (c : Fin k)
    (i : Fin m) (j : Fin k) :
    GaussAdaptSerialize64.finalBank
      (GaussAdaptPrepare64.prepared S (decide (i = r)))
      (GaussAdaptedPacket64.packet (decide (i = r))
        (encodeRawRat (GaussPhysical.rawOfRat
          (B (GaussCellSourceBridge.sourceRow r pivot i) j)))
        (encodeRawRat (GaussPhysical.rawOfRat
          (B (GaussCellSourceBridge.sourceRow r pivot i) c)))
        (encodeRawRat (GaussPhysical.rawOfRat
          (B (GaussCellSourceBridge.sourceRow r pivot r) j)))
        (encodeRawRat (GaussPhysical.rawOfRat
          (B (GaussCellSourceBridge.sourceRow r pivot r) c))))
      (fun _ => []) 23 =
    GaussUniformCellAlgebra.adaptedSourceCellPacket B r pivot c i j := by
  rw [GaussAdaptedPacket64.output_at_23]
  exact source_cell_named B r pivot c i j

#print axioms packet_named
#print axioms source_cell_named
#print axioms output_source_cell_named

end CurrentAdditive.GaussAdaptedNamedBridge64
