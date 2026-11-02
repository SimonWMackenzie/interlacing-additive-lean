import CurrentAdditive.GaussAdaptedPacket64
import CurrentAdditive.GaussRequestTypedBridge64

/-! Semantic bridge in the production RawRat module environment. -/

namespace CurrentAdditive.GaussAdaptedPacket64

open CurrentAdditive.CodeDCodec
open EthInapproximability.CurrentPaper
open Turing
open BitMachineEncoding

/-- The exact expression defining `GaussUniformCellAlgebra.adaptedPacket` in
its frozen scratch source. Kept local because that legacy scratch module imports
an incompatible duplicate of `CodeDCodec`. -/
def sourceAdaptedPacket (flag : Bool)
    (current column row pivot : RawRat) : List Bool :=
  GaussPhysical.cellPacket false
    (if flag then CodeDCanonicalSource.rawOfRat 0 else current)
    (if flag then CodeDCanonicalSource.rawOfRat (-1) else column)
    row pivot

theorem packet_eq_sourceAdaptedPacket (flag : Bool)
    (current column row pivot : RawRat) :
    packet flag (encodeRawRat current) (encodeRawRat column)
      (encodeRawRat row) (encodeRawRat pivot) =
    sourceAdaptedPacket flag current column row pivot := by
  cases flag with
  | false =>
      simpa [packet, selectedCurrent, selectedColumn,
        sourceAdaptedPacket] using
        (GaussRequestTypedBridge64.packet_eq_cellPacket false
          current column row pivot)
  | true =>
      simpa [packet, selectedCurrent, selectedColumn,
        GaussAdaptPrepare64.zeroWord, GaussAdaptPrepare64.minusOneWord,
        sourceAdaptedPacket] using
        (GaussRequestTypedBridge64.packet_eq_cellPacket false
          (CodeDCanonicalSource.rawOfRat 0)
          (CodeDCanonicalSource.rawOfRat (-1)) row pivot)

theorem run_sourceAdaptedPacket (S : Stack → List Bool) (flag : Bool)
    (current column row pivot : RawRat)
    (hflag : S 28 = [flag])
    (hcurrent : S 24 = encodeRawRat current)
    (hcolumn : S 25 = encodeRawRat column)
    (hrow : S 26 = encodeRawRat row)
    (hpivot : S 27 = encodeRawRat pivot)
    (hempty : ∀ j : Stack, j.val < 7 → S j = [])
    (h21 : S 21 = []) (h22 : S 22 = []) (h23 : S 23 = []) :
    ∃ t ≤ timeBound flag (encodeRawRat current) (encodeRawRat column)
      (encodeRawRat row) (encodeRawRat pivot),
      ((advance program)^[t])
        (⟨some start, initialControl, S⟩ : Config) =
      ⟨none, initialControl,
        GaussAdaptSerialize64.finalBank
          (GaussAdaptPrepare64.prepared S flag)
          (sourceAdaptedPacket flag current column row pivot)
          (fun _ => [])⟩ := by
  obtain ⟨t, ht, hr⟩ := run_full S flag
    (encodeRawRat current) (encodeRawRat column)
    (encodeRawRat row) (encodeRawRat pivot)
    hflag hcurrent hcolumn hrow hpivot hempty h21 h22 h23
  refine ⟨t, ht, ?_⟩
  simpa only [packet_eq_sourceAdaptedPacket] using hr

#print axioms packet_eq_sourceAdaptedPacket
#print axioms run_sourceAdaptedPacket

end CurrentAdditive.GaussAdaptedPacket64
