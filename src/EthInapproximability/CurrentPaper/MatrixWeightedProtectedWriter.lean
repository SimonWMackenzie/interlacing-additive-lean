import EthInapproximability.CurrentPaper.MatrixWeightedArithmetic
import EthInapproximability.CurrentPaper.MatrixTableWriter

/-!
# Exact writer-facing contract for the current protected matrix

This owner connects the physical row-major writer to the *actual* protected
matrix under the explicit 182:2 and four-support decoders.  The `EntryRuns`
hypothesis is deliberately visible: a single fixed weighted cell callback
that constructs these decoded labels from raw input remains outstanding.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedProtectedWriter

open Construction MatrixWeightedArithmetic MatrixWeightedTable MatrixMaterialization

variable {rx cy : ℕ}

def protectedEntry (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (x y : ℕ) : Bool :=
  if hx : x < Fintype.card (ProtectedColumns a s q (Fin cy)) then
    if hy : y < Fintype.card (ProtectedRows s L nv nb (Fin rx)) then
      protectedMatrix R a s q L nv nb hs family order vectors cap
        (typedColumn (rawColumnCode' a s q cy) (diagonalCode a s q cy)
          (uniformCopies (Y := Fin cy) a s q) ⟨x, hx⟩)
        (typedRow (rawRowCode s L nv nb rx order) (templateCode s L)
          (vertexCode nv rx) (auxiliaryCode nb rx) ⟨y, hy⟩)
    else false
  else false

theorem protectedEntry_inbounds (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (x : Fin (Fintype.card (ProtectedColumns a s q (Fin cy))))
    (y : Fin (Fintype.card (ProtectedRows s L nv nb (Fin rx)))) :
    protectedEntry R a s q L nv nb hs family order vectors cap x.val y.val =
      protectedMatrix R a s q L nv nb hs family order vectors cap
        (typedColumn (rawColumnCode' a s q cy) (diagonalCode a s q cy)
          (uniformCopies (Y := Fin cy) a s q) x)
        (typedRow (rawRowCode s L nv nb rx order) (templateCode s L)
          (vertexCode nv rx) (auxiliaryCode nb rx) y) := by
  simp only [protectedEntry, dif_pos x.isLt, dif_pos y.isLt]

/-- Once a fixed callback satisfies the displayed `EntryRuns`, the existing
writer physically emits the literal current protected matrix in its final
transposed orientation, while preserving any prior output suffix. -/
theorem write_protected {K : ℕ} {Label Control : Type*}
    (P : Label → Turing.TM2.Stmt
      (fun _ : MatrixTableWriter.CellStack K => Bool) Label Control)
    (start : Label) (initial : Control) (bank : Fin K → List Bool)
    (T : ℕ) (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (hcell : MatrixTableWriter.EntryRuns P start initial bank
      (Fintype.card (ProtectedColumns a s q (Fin cy)))
      (Fintype.card (ProtectedRows s L nv nb (Fin rx))) T
      (protectedEntry R a s q L nv nb hs family order vectors cap))
    (output : List Bool) :
    ∃ t ≤ MatrixTableWriter.writerBound
        (Fintype.card (ProtectedColumns a s q (Fin cy)))
        (Fintype.card (ProtectedRows s L nv nb (Fin rx))) T, ∃ v,
      MatrixTableWriter.run P start initial t
        (MatrixTableWriter.cfg (some (.inr (.copy .rows))) (initial, none)
          (MatrixTableWriter.ready bank
            (Fintype.card (ProtectedColumns a s q (Fin cy)))
            (Fintype.card (ProtectedRows s L nv nb (Fin rx)))
            0 0 0 0 [] output)) =
      MatrixTableWriter.cfg none v
        (MatrixTableWriter.ready bank
          (Fintype.card (ProtectedColumns a s q (Fin cy)))
          (Fintype.card (ProtectedRows s L nv nb (Fin rx)))
          0 0 0 0 []
          (rowMajor (fun x y => protectedMatrix R a s q L nv nb hs
            family order vectors cap
              (typedColumn (rawColumnCode' a s q cy) (diagonalCode a s q cy)
                (uniformCopies (Y := Fin cy) a s q) x)
              (typedRow (rawRowCode s L nv nb rx order) (templateCode s L)
                (vertexCode nv rx) (auxiliaryCode nb rx) y)) ++ output)) := by
  exact MatrixTableWriter.write_rowMajor P start initial bank _ _ T
    (protectedEntry R a s q L nv nb hs family order vectors cap)
    _ (protectedEntry_inbounds R a s q L nv nb hs family order vectors cap)
    hcell output

end EthInapproximability.CurrentPaper.MatrixWeightedProtectedWriter
