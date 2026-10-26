import CurrentAdditive.V38PrinterEntry

namespace CurrentAdditive.V38TablePrinter

open CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open EthInapproximability.CurrentPaper
open CurrentAdditive.SmallBias

def natEntry {v e : ℕ} (b t d modulus : ℕ) (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (x y : ℕ) : Bool :=
  if hx : x < rowCount v b t then
    if hy : y < columnCount b t d then
      entry b t d modulus he edges ⟨x, hx⟩ ⟨y, hy⟩
    else false
  else false

theorem natEntry_fin {v e : ℕ} (b t d modulus : ℕ) (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (x : Fin (rowCount v b t)) (y : Fin (columnCount b t d)) :
    natEntry b t d modulus he edges x.val y.val =
      entry b t d modulus he edges x y := by
  simp [natEntry]

/-- The generic physical writer's row-major target is *exactly* the bits
of the computable canonical table. This theorem does not supply its cell
subroutine or count that subroutine's transitions. -/
theorem tableWord_eq_canonical_bits {v e : ℕ} (b t d modulus : ℕ)
    (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) :
    MatrixTableWriter.tableWord (natEntry b t d modulus he edges)
      (columnCount b t d) 0 (rowCount v b t) =
      (table b t d modulus he edges).bits := by
  calc
    _ = MatrixMaterialization.rowMajor (entry b t d modulus he edges) :=
      MatrixTableWriter.tableWord_eq_rowMajor _ _ _ _
        (natEntry_fin b t d modulus he edges)
    _ = (table b t d modulus he edges).bits := rfl

theorem writerBound_public_polynomial (v b t T : ℕ) (ht : 4 ≤ t) :
    MatrixTableWriter.writerBound
      (rowCount v b t) (columnCount b t (publicFieldDegree b t)) T ≤
      20 * (rowCount v b t +
        columnCount b t (publicFieldDegree b t) + T + 1) ^ 3 :=
  MatrixTableWriter.writerBound_polynomial _ _ _

#print axioms tableWord_eq_canonical_bits
#print axioms writerBound_public_polynomial

end CurrentAdditive.V38TablePrinter
