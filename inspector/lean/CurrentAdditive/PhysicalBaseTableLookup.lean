import CurrentAdditive.RawRationalPacket
import EthInapproximability.CurrentPaper.MatrixTableLookup

/-! A physical row-major table-read callback for the validated base packet.
The callback receives unary coordinates; conversion from compact encoded
indices into these coordinates is a separate machine stage. -/

namespace Paper2.PhysicalBaseTableLookup

open Paper2.CompactRationalPacket Paper2.YaoMaterialization
open EthInapproximability.CurrentPaper

theorem packet_lookup_run {rows cols : ℕ} (P : Packet rows cols)
    (i : Fin rows) (j : Fin cols) (out : List Bool) :
    ∃ t ≤ 32 * (i.val + cols + j.val + P.table.bits.length + 1) ^ 2,
      MatrixTableLookup.run t
        (MatrixTableLookup.cfg (some MatrixTableLookup.start)
          MatrixTableLookup.initial
          (List.replicate i.val true) (List.replicate cols true)
          (List.replicate j.val true) [] P.table.bits out) =
        MatrixTableLookup.cfg none MatrixTableLookup.initial
          (List.replicate i.val true) (List.replicate cols true)
          (List.replicate j.val true) [] P.table.bits
          (P.table.matrix i j :: out) := by
  have hb : i.val * cols + j.val < P.table.bits.length := by
    rw [P.table.length]
    have h := (rowMajorIndex i j).isLt
    simpa only [rowMajorIndex_value] using h
  have he : P.table.bits[i.val * cols + j.val]?.getD false =
      P.table.matrix i j := by
    simp only [List.getElem?_eq_getElem hb, Option.getD_some,
      SerializedTable.matrix, List.get_eq_getElem,
      Fin.val_cast, rowMajorIndex_value]
  simpa only [he] using
    MatrixTableLookup.lookup_run i.val cols j.val P.table.bits out

theorem raw_packet_lookup_run {rows cols : ℕ}
    (R : Paper2.RawRationalPacket.RawPacket rows cols)
    (P : Packet rows cols) (h : R.compile? = some P)
    (i : Fin rows) (j : Fin cols) (out : List Bool) :
    ∃ t ≤ 32 * (i.val + cols + j.val + R.bits.length + 1) ^ 2,
      MatrixTableLookup.run t
        (MatrixTableLookup.cfg (some MatrixTableLookup.start)
          MatrixTableLookup.initial
          (List.replicate i.val true) (List.replicate cols true)
          (List.replicate j.val true) [] R.bits out) =
        MatrixTableLookup.cfg none MatrixTableLookup.initial
          (List.replicate i.val true) (List.replicate cols true)
          (List.replicate j.val true) [] R.bits
          (P.table.matrix i j :: out) := by
  have he := (R.compiled_fields P h).1
  simpa only [he] using packet_lookup_run P i j out

#print axioms packet_lookup_run
#print axioms raw_packet_lookup_run

end Paper2.PhysicalBaseTableLookup
