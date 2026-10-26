import CurrentAdditive.V38EncodedTable
import CurrentAdditive.CanonicalPrintedTable

/-!
Private v38 row-major entry adapter. The old executable source position
decoder has a sentinel 0; this file maps that sentinel to the manuscript's
constant-zero output and maps real positions 1..K to the K printed array bits.
No neutral array coordinate is generated.
-/

namespace CurrentAdditive.V38Executable

open CurrentAdditive.SmallBias
open CurrentAdditive.FiniteFieldConstructor
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol
open Paper2.YaoMaterialization
open Paper2.EncodedSelectedOutput
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

def wordAtPosition {H K n : ℕ}
    (W : Fin n → Fin H × Fin K → Bool)
    (ℓ : Fin n) (a : Fin H) (p : Fin (K + 1)) : Bool :=
  if h : p.val = 0 then false
  else W ℓ (a, ⟨p.val - 1, by omega⟩)

theorem wordAtPosition_eq_v38WithZero {H K n : ℕ}
    (W : Fin n → Fin H × Fin K → Bool)
    (ℓ : Fin n) (a : Fin H) (p : Fin (K + 1)) :
    wordAtPosition W ℓ a p = v38WithZero W ℓ (a, p) := by
  cases p using Fin.cases with
  | zero => simp [wordAtPosition]
  | succ i =>
    simp only [wordAtPosition, Fin.val_succ, Nat.succ_ne_zero, ↓reduceDIte,
      Nat.succ_sub_one, v38WithZero_succ]

/-- A computable entry function for the exact v38 zero-off-edge table. -/
def entry {v e : ℕ} (b t d modulus : ℕ) (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) :
    Fin (CanonicalTable.rowCount v b t) →
      Fin (CanonicalTable.columnCount b t d) → Bool :=
  fun i j =>
    let row := (CanonicalTable.rowIndex v b t).symm i
    let col := (CanonicalTable.columnIndex b t d).symm j
    wordAtPosition (v38PrintedPairWord b t d modulus) col.2.2
      (CanonicalTable.selector (2 ^ (t - 1)) (2 ^ b) row.2 col.1)
      (CanonicalTable.position he edges col.2.1 row.1)

def table {v e : ℕ} (b t d modulus : ℕ) (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) :
    SerializedTable (CanonicalTable.rowCount v b t)
      (CanonicalTable.columnCount b t d) :=
  tabulate (entry b t d modulus he edges)

theorem entry_eq_matrix {v e : ℕ} (b t d modulus : ℕ)
    (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (CanonicalTable.rowCount v b t))
    (j : Fin (CanonicalTable.columnCount b t d)) :
    entry b t d modulus he edges i j =
      matrixV38 (placeEdges edges (Fin.castLEEmb he))
        (fullSelector (2 ^ (t - 1)) (2 ^ b))
        (v38PrintedPairWord b t d modulus)
        ((SmallBias.printedRowIndex v b t).symm
          (CanonicalTable.rowRelabel v b t i))
        ((SmallBias.printedColumnIndex b t d).symm j) := by
  simp only [entry, matrixV38, Paper2.YaoLookup.matrix,
    CanonicalTable.rowRelabel, CanonicalTable.rowIndex,
    CanonicalTable.columnIndex,
    SmallBias.printedRowIndex, SmallBias.printedColumnIndex,
    Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply]
  simp only [Prod.map]
  rw [CanonicalTable.fullSelector_relabel, CanonicalTable.position_eq_source]
  simp only [Equiv.refl_apply]
  exact wordAtPosition_eq_v38WithZero _ _ _ _

theorem table_Dalt {v e : ℕ} (b t d modulus : ℕ)
    (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (starter : Turn) :
    Dalt starter (table b t d modulus he edges).matrix =
      Dalt starter (matrixV38 (placeEdges edges (Fin.castLEEmb he))
        (fullSelector (2 ^ (t - 1)) (2 ^ b))
        (v38PrintedPairWord b t d modulus)) := by
  have heq : (table b t d modulus he edges).matrix =
      fun i j => matrixV38 (placeEdges edges (Fin.castLEEmb he))
        (fullSelector (2 ^ (t - 1)) (2 ^ b))
        (v38PrintedPairWord b t d modulus)
        ((SmallBias.printedRowIndex v b t).symm
          (CanonicalTable.rowRelabel v b t i))
        ((SmallBias.printedColumnIndex b t d).symm j) := by
    funext i j
    exact (tabulate_matrix _ i j).trans
      (entry_eq_matrix b t d modulus he edges i j)
  rw [heq]
  exact Dalt_comap_equiv starter _
    ((CanonicalTable.rowRelabel v b t).trans
      (SmallBias.printedRowIndex v b t).symm)
    (SmallBias.printedColumnIndex b t d).symm

def instanceOfTable {v e : ℕ} (b t d modulus : ℕ) (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) :
    EthInapproximability.CurrentPaper.EncodedCommunication.Instance :=
  Paper2.EncodedSelectedOutput.instanceOf (table b t d modulus he edges)
    (2 * b + 4 * t + 2)

theorem instanceOfTable_valid {v e : ℕ} (hv : 0 < v)
    (b t d modulus : ℕ) (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) :
    (instanceOfTable b t d modulus he edges).Valid := by
  apply instanceOf_valid
  · unfold CanonicalTable.rowCount
    positivity
  · unfold CanonicalTable.columnCount
    positivity

theorem instanceOfTable_Dalt {v e : ℕ} (b t d modulus : ℕ)
    (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (starter : Turn) :
    Dalt starter (ProtocolVerifier.tableGame
      (instanceOfTable b t d modulus he edges).rows
      (instanceOfTable b t d modulus he edges).cols
      (instanceOfTable b t d modulus he edges).table) =
      Dalt starter (matrixV38 (placeEdges edges (Fin.castLEEmb he))
        (fullSelector (2 ^ (t - 1)) (2 ^ b))
        (v38PrintedPairWord b t d modulus)) := by
  rw [show ProtocolVerifier.tableGame
      (instanceOfTable b t d modulus he edges).rows
      (instanceOfTable b t d modulus he edges).cols
      (instanceOfTable b t d modulus he edges).table =
      (table b t d modulus he edges).matrix by
        exact tableGame_eq_matrix _]
  exact table_Dalt b t d modulus he edges starter

/-- Conditional theorem for the actual row-major entry and serialized table.
The only external input is `G : GLSourceInput t`; no constructor for `G`
is asserted. The selected array list and modulus depend on b,t only. -/
theorem selected_executable_table_costs {t : ℕ}
    (G : CurrentAdditive.V38Source.GLSourceInput t)
    (input : List Bool) (ht : 4 ≤ t) :
    let src := CurrentAdditive.V38Source.selectedSource G input
    let b := CurrentAdditive.V38Encoded.edgeBits src.2.1
    let he := CurrentAdditive.V38Encoded.edgeCount_le_capacity src.2.1
    ∃ output : List (ℕ × ℕ × List Bool), ∃ modulus : ℕ,
      TrialSearch.makeList (v38FieldDegree b t) (v38PositionCount b t) = some output ∧
      TrialSearch.firstPassing (v38FieldDegree b t) = some modulus ∧
      output = StreamingPrinter.labelledWords (v38FieldDegree b t)
        modulus (v38PositionCount b t) ∧
      (input ∈ G.L →
        Dalt .alice (table b t (v38FieldDegree b t) modulus
          he src.2.2).matrix ≤ 2 * b + 4 * t + 2) ∧
      (input ∉ G.L →
        (2 * b + 4 * t + 2) + 2 * t - 8 ≤
          Dalt .alice (table b t (v38FieldDegree b t) modulus
            he src.2.2).matrix) := by
  dsimp only
  let src := CurrentAdditive.V38Source.selectedSource G input
  let b := CurrentAdditive.V38Encoded.edgeBits src.2.1
  let he := CurrentAdditive.V38Encoded.edgeCount_le_capacity src.2.1
  obtain ⟨output, modulus, houtput, hmodulus, hout, hyes, hno⟩ :=
    CurrentAdditive.V38Encoded.selected_printed_table_costs G input ht
  refine ⟨output, modulus, houtput, hmodulus, hout, ?_, ?_⟩
  · intro hy
    have heq : Dalt .alice
        (table b t (v38FieldDegree b t) modulus he src.2.2).matrix =
        Dalt .alice
          (CurrentAdditive.V38Encoded.printedTable b t
            (v38FieldDegree b t) modulus src.2.2
            (CurrentAdditive.V38Encoded.sourceIndex G input)).matrix := by
      rw [table_Dalt, CurrentAdditive.V38Encoded.printedTable_Dalt]
      rfl
    rw [heq]
    exact hyes hy
  · intro hn
    have heq : Dalt .alice
        (table b t (v38FieldDegree b t) modulus he src.2.2).matrix =
        Dalt .alice
          (CurrentAdditive.V38Encoded.printedTable b t
            (v38FieldDegree b t) modulus src.2.2
            (CurrentAdditive.V38Encoded.sourceIndex G input)).matrix := by
      rw [table_Dalt, CurrentAdditive.V38Encoded.printedTable_Dalt]
      rfl
    rw [heq]
    exact hno hn

#print axioms wordAtPosition_eq_v38WithZero
#print axioms entry_eq_matrix
#print axioms table_Dalt
#print axioms instanceOfTable_valid
#print axioms instanceOfTable_Dalt
#print axioms selected_executable_table_costs

end CurrentAdditive.V38Executable
