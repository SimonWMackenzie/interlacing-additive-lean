import CurrentAdditive.CanonicalEdgeSlots

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open CurrentAdditive.SmallBias
open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol
open Paper2.YaoMaterialization
open Paper2.YaoLowerBound.Materialization
open Paper2.EncodedSelectedOutput
open EthInapproximability.CurrentPaper.EncodedCommunication

def rowCount (v b t : ℕ) : ℕ :=
  v * (2 ^ b) ^ (2 ^ (t - 1))

def columnCount (b t d : ℕ) : ℕ :=
  2 ^ (t - 1) * 2 ^ b * (2 ^ d) ^ 2

def rowIndex (v b t : ℕ) :
    (Fin v × Fin ((2 ^ b) ^ (2 ^ (t - 1)))) ≃ Fin (rowCount v b t) :=
  finProdFinEquiv

def columnIndex (b t d : ℕ) :
    (Fin (2 ^ (t - 1)) × Fin (2 ^ b) × Fin ((2 ^ d) ^ 2)) ≃
      Fin (columnCount b t d) :=
  tripleIndex _ _ _

/-- One fully executable matrix entry. Its selector and edge positions are
decoded from numerical labels, then the already checked finite-field bit
printer supplies the payload bit. -/
def entry {v e : ℕ} (b t d modulus : ℕ) (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) :
    Fin (rowCount v b t) → Fin (columnCount b t d) → Bool :=
  fun i j =>
    let row := (rowIndex v b t).symm i
    let col := (columnIndex b t d).symm j
    printedPairFieldWord b t d modulus col.2.2
      (selector (2 ^ (t - 1)) (2 ^ b) row.2 col.1,
        position he edges col.2.1 row.1)

def table {v e : ℕ} (b t d modulus : ℕ) (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) :
    SerializedTable (rowCount v b t) (columnCount b t d) :=
  tabulate (entry b t d modulus he edges)

def instanceOfTable {v e : ℕ} (b t d modulus : ℕ) (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) : Instance :=
  instanceOf (table b t d modulus he edges) (2 * b + 4 * t + 2)

/-- The old selector labels are an arbitrary permutation of our numerical
base-`H` labels. This equivalence is used only in the proof, not the printer. -/
noncomputable def rowRelabel (v b t : ℕ) :
    Fin (rowCount v b t) ≃ Fin (printedRowCount v b t) :=
  (rowIndex v b t).symm |>.trans
    ((Equiv.refl (Fin v)).prodCongr
      (selectorRelabel (2 ^ (t - 1)) (2 ^ b))) |>.trans
    (printedRowIndex v b t)

theorem entry_eq_printed_matrix {v e : ℕ} (b t d modulus : ℕ)
    (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v b t)) (j : Fin (columnCount b t d)) :
    entry b t d modulus he edges i j =
      matrix (placeEdges edges (Fin.castLEEmb he))
        (fullSelector (2 ^ (t - 1)) (2 ^ b))
        (printedPairFieldWord b t d modulus)
        ((printedRowIndex v b t).symm (rowRelabel v b t i))
        ((printedColumnIndex b t d).symm j) := by
  simp only [entry, matrix, rowRelabel, rowIndex, columnIndex,
    printedRowIndex, printedColumnIndex, Equiv.trans_apply,
    Equiv.symm_apply_apply, Equiv.prodCongr_apply]
  simp only [Prod.map]
  rw [fullSelector_relabel, position_eq_source]
  simp only [Equiv.refl_apply]
  rfl

theorem table_Dalt {v e : ℕ} (b t d modulus : ℕ)
    (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (starter : Turn) :
    Dalt starter (table b t d modulus he edges).matrix =
      Dalt starter (matrix (placeEdges edges (Fin.castLEEmb he))
        (fullSelector (2 ^ (t - 1)) (2 ^ b))
        (printedPairFieldWord b t d modulus)) := by
  have heq : (table b t d modulus he edges).matrix =
      fun i j => matrix (placeEdges edges (Fin.castLEEmb he))
        (fullSelector (2 ^ (t - 1)) (2 ^ b))
        (printedPairFieldWord b t d modulus)
        ((printedRowIndex v b t).symm (rowRelabel v b t i))
        ((printedColumnIndex b t d).symm j) := by
    funext i j
    exact (tabulate_matrix _ i j).trans
      (entry_eq_printed_matrix b t d modulus he edges i j)
  rw [heq]
  exact Dalt_comap_equiv starter _
    ((rowRelabel v b t).trans (printedRowIndex v b t).symm)
    (printedColumnIndex b t d).symm

#print axioms entry_eq_printed_matrix
#print axioms table_Dalt

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
