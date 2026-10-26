import CurrentAdditive.GaussFetchFromBackups64
import CurrentAdditive.GaussTypedPacket

namespace CurrentAdditive.GaussTypedCellAddress
open EthInapproximability.CurrentPaper

theorem split_map_finRange {α : Type*} {n : Nat}
    (f : Fin n → α) (i : Fin n) :
    (List.finRange n).map f =
      ((List.finRange n).map f).take i.val ++
        f i :: ((List.finRange n).map f).drop (i.val+1) := by
  let xs := (List.finRange n).map f
  have hi : i.val < xs.length := by simpa [xs] using i.isLt
  have he : xs[i.val] = f i := by simp [xs]
  rw [← he, List.getElem_cons_drop hi, List.take_append_drop]

theorem cell_at {m k : Nat} (B : Fin m → Fin k → ℚ)
    (i : Fin m) (j : Fin k) :
    GaussFetchFromBackups64.CellAt (GaussPhysical.encodeTypedMatrix B)
      i.val j.val (CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B i j))) := by
  let cell := fun (a : Fin m) (b : Fin k) =>
    CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B a b))
  let rows := (List.finRange m).map fun a =>
    SourceListEncoding.encode ((List.finRange k).map (cell a))
  let cells := (List.finRange k).map (cell i)
  refine ⟨rows.take i.val,rows.drop (i.val+1),
    cells.take j.val,cells.drop (j.val+1),?_,?_,?_⟩
  · have hr := split_map_finRange
      (fun a => SourceListEncoding.encode ((List.finRange k).map (cell a))) i
    have hc := split_map_finRange (cell i) j
    change GaussPhysical.encodeTypedMatrix B =
      SourceListEncoding.encode
        (rows.take i.val ++ SourceListEncoding.encode
          (cells.take j.val ++ cell i j :: cells.drop (j.val+1)) :: rows.drop (i.val+1))
    rw [← hc, ← hr]
    simp [GaussPhysical.encodeTypedMatrix, GaussPhysical.encodeRationalMatrix,
      GaussPhysical.encodeMatrix,GaussPhysical.encodeRow,GaussPhysical.typedRows,
      CodeDCodecV2.encodeItems,rows,cells,cell,List.map_map,Function.comp_def]
  · simp [rows,Nat.min_eq_left (Nat.le_of_lt i.isLt)]
  · simp [cells,Nat.min_eq_left (Nat.le_of_lt j.isLt)]

#print axioms cell_at
end CurrentAdditive.GaussTypedCellAddress
