import Paper2.ASquareSideWrite
import Paper2.ASquare

/-!
# U17: the joined side+writer program prints exactly the square instance's table

Lane `owner:a-square-1` (private, 26 September 2026). For every VALID instance
`I = ⟨r, c, thr, bits⟩` (`r, c > 0`, `bits.length = r*c`), the joined program
`SideWrite.program`, started on the writer bank `unary r, unary c, bits` with empty counters,
writes exactly `(ASquare.squareInstance I).table` (in front of an arbitrary old output), and leaves
`unary (squareInstance I).rows` in both counters. So the remaining content of the OPEN contract
`ASquare.SquarePost` is only the parser (instance word -> this bank), the header serializer
(`natField side ++ natField side ++ natField thr` in front of the table) and the machine wrapper.
Does not close a ledger row.
-/

namespace Paper2.ASquare.InstanceWrite

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

/-- A row-major word of the right length is the row-major serialization of its own decoded table. -/
theorem rowMajor_tableGame {r c : ℕ} (hc : 0 < c) (bits : List Bool) (hlen : bits.length = r * c) :
    MatrixMaterialization.rowMajor (ProtocolVerifier.tableGame r c bits) = bits := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < r * c
  · have hq : k / c < r := by
      rw [Nat.div_lt_iff_lt_mul hc]; exact hk
    have hrm : k % c < c := Nat.mod_lt _ hc
    have hdecomp : k / c * c + k % c = k := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod k c
    have h := MatrixMaterialization.rowMajor_entry (ProtocolVerifier.tableGame r c bits)
      ⟨k / c, hq⟩ ⟨k % c, hrm⟩
    simp only at h
    rw [hdecomp] at h
    rw [h]
    simp only [ProtocolVerifier.tableGame, ProtocolVerifier.tableEntry]
    rw [hdecomp]
    have hkb : k < bits.length := by rw [hlen]; exact hk
    rw [List.getElem?_eq_getElem hkb]
    rfl
  · have h1 : (MatrixMaterialization.rowMajor (ProtocolVerifier.tableGame r c bits)).length ≤ k := by
      rw [MatrixMaterialization.rowMajor_length]; omega
    have h2 : bits.length ≤ k := by rw [hlen]; omega
    rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2]

/-- **The square instance's table, printed by the joined program.** -/
theorem instance_write (I : EncodedCommunication.Instance) (hI : I.Valid) (output : List Bool) :
    ∃ t ≤ Side.sideBound I.rows I.cols +
        MatrixTableWriter.writerBound (SquarePadding.side I.rows I.cols)
          (SquarePadding.side I.rows I.cols)
          (Unit4Shell.SquareWriter.callbackBound (SquarePadding.side I.rows I.cols)
            (SquarePadding.side I.rows I.cols) I.rows I.cols (I.rows * I.cols)) + 1, ∃ v,
      ((advance SideWrite.program)^[t])
        ⟨some SideWrite.start, SideWrite.initial,
          (MatrixTableWriter.ready
            (Unit4Shell.SquareWriter.persistentBank I.rows I.cols I.table)
            0 0 0 0 0 0 [] output).contents⟩ =
      ⟨none, v,
          (MatrixTableWriter.ready
            (Unit4Shell.SquareWriter.persistentBank I.rows I.cols I.table)
            (squareInstance I).rows (squareInstance I).cols 0 0 0 0 []
            ((squareInstance I).table ++ output)).contents⟩ := by
  obtain ⟨hr, hc, hlen⟩ := hI
  have hb := rowMajor_tableGame hc I.table hlen
  obtain ⟨t, ht, v, h⟩ := SideWrite.side_write hr hc
    (ProtocolVerifier.tableGame I.rows I.cols I.table) output
  rw [hb] at h
  refine ⟨t, ht, v, ?_⟩
  have htab : (squareInstance I).table =
      MatrixMaterialization.rowMajor
        (SquarePadding.matrix hr hc (ProtocolVerifier.tableGame I.rows I.cols I.table)) := by
    change MatrixMaterialization.rowMajor (squareFun I.rows I.cols I.table) = _
    rw [squareFun_eq_matrix hr hc]
  rw [htab]
  exact h

#print axioms rowMajor_tableGame
#print axioms instance_write

end Paper2.ASquare.InstanceWrite
