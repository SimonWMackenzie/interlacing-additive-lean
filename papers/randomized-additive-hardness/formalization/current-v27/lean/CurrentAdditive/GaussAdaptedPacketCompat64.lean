import CurrentAdditive.GaussAdaptedPacketSemantic64

/-! A compatible restatement of the three frozen adapted-packet definitions.
The source of these bodies is the hash-pinned GaussUniformCellAlgebra.lean.
The original module cannot coexist with the production codec import graph. -/

namespace CurrentAdditive.GaussUniformCellAlgebraCompat

open CurrentAdditive.CodeDCodec

def adaptedCurrent (flag : Bool) (current : RawRat) : RawRat :=
  if flag then CodeDCanonicalSource.rawOfRat 0 else current

def adaptedColumn (flag : Bool) (column : RawRat) : RawRat :=
  if flag then CodeDCanonicalSource.rawOfRat (-1) else column

def adaptedPacket (flag : Bool) (current column row pivot : RawRat) : List Bool :=
  GaussPhysical.cellPacket false
    (adaptedCurrent flag current) (adaptedColumn flag column) row pivot

def sourceRow {m : Nat} (r pivot i : Fin m) : Fin m :=
  Equiv.swap r pivot i

def adaptedSourceCellPacket {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (i : Fin m) (j : Fin k) : List Bool :=
  adaptedPacket (decide (i = r))
    (GaussPhysical.rawOfRat
      (B (sourceRow r pivot i) j))
    (GaussPhysical.rawOfRat
      (B (sourceRow r pivot i) c))
    (GaussPhysical.rawOfRat
      (B (sourceRow r pivot r) j))
    (GaussPhysical.rawOfRat
      (B (sourceRow r pivot r) c))

end CurrentAdditive.GaussUniformCellAlgebraCompat

namespace CurrentAdditive.GaussAdaptedPacket64

open CurrentAdditive.CodeDCodec

theorem packet_eq_compat_adaptedPacket (flag : Bool)
    (current column row pivot : RawRat) :
    packet flag (encodeRawRat current) (encodeRawRat column)
      (encodeRawRat row) (encodeRawRat pivot) =
    GaussUniformCellAlgebraCompat.adaptedPacket
      flag current column row pivot := by
  rw [packet_eq_sourceAdaptedPacket]
  rfl

theorem packet_eq_compat_adaptedSourceCellPacket {m k : Nat}
    (B : Fin m → Fin k → ℚ) (r pivot : Fin m) (c : Fin k)
    (i : Fin m) (j : Fin k) :
    packet (decide (i = r))
      (encodeRawRat (GaussPhysical.rawOfRat
        (B (GaussUniformCellAlgebraCompat.sourceRow r pivot i) j)))
      (encodeRawRat (GaussPhysical.rawOfRat
        (B (GaussUniformCellAlgebraCompat.sourceRow r pivot i) c)))
      (encodeRawRat (GaussPhysical.rawOfRat
        (B (GaussUniformCellAlgebraCompat.sourceRow r pivot r) j)))
      (encodeRawRat (GaussPhysical.rawOfRat
        (B (GaussUniformCellAlgebraCompat.sourceRow r pivot r) c))) =
    GaussUniformCellAlgebraCompat.adaptedSourceCellPacket
      B r pivot c i j := by
  rw [packet_eq_compat_adaptedPacket]
  rfl

#print axioms packet_eq_compat_adaptedPacket
#print axioms packet_eq_compat_adaptedSourceCellPacket

end CurrentAdditive.GaussAdaptedPacket64
