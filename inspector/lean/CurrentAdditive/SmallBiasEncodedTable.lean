import CurrentAdditive.SmallBiasSourceBridge
import Paper2.EncodedSelectedOutput
import Paper2.YaoMaterializationTape

/-!
# Row-major encoded table for the public printed matrix

Source: v27 Section 7 `yao:dimensions`, `yao:main`, and `yao:bpp`.
This is a semantic and list-level table materialization. Its data bits
are the actual printed-pair bit function; a physical all-input polynomial
machine for the whole source-to-table map is a separate obligation.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol
open Paper2.YaoMaterialization Paper2.EncodedSelectedOutput
open Paper2.YaoLowerBound.Materialization
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

def printedRowCount (v b t : ℕ) : ℕ :=
  v * Fintype.card (Fin (2 ^ (t - 1)) → Fin (2 ^ b))

def printedColumnCount (b t d : ℕ) : ℕ :=
  2 ^ (t - 1) * 2 ^ b * (2 ^ d) ^ 2

def printedRowIndex (v b t : ℕ) :
    (Fin v × Fin (Fintype.card (Fin (2 ^ (t - 1)) → Fin (2 ^ b)))) ≃
      Fin (printedRowCount v b t) := finProdFinEquiv

def printedColumnIndex (b t d : ℕ) :
    (Fin (2 ^ (t - 1)) × Fin (2 ^ b) × Fin ((2 ^ d) ^ 2)) ≃
      Fin (printedColumnCount b t d) := tripleIndex _ _ _

/-- All entries are read in the canonical row-major order. -/
noncomputable def printedTable {v e : ℕ} (b t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (index : Fin e ↪ Fin (2 ^ b)) :
    SerializedTable (printedRowCount v b t) (printedColumnCount b t d) :=
  tabulate fun i j =>
    matrix (placeEdges edges index)
      (fullSelector (2 ^ (t - 1)) (2 ^ b))
      (printedPairFieldWord b t d modulus)
      ((printedRowIndex v b t).symm i)
      ((printedColumnIndex b t d).symm j)

theorem printedTable_Dalt {v e : ℕ} (b t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (index : Fin e ↪ Fin (2 ^ b)) (starter : Turn) :
    Dalt starter (printedTable b t d modulus edges index).matrix =
      Dalt starter (matrix (placeEdges edges index)
        (fullSelector (2 ^ (t - 1)) (2 ^ b))
        (printedPairFieldWord b t d modulus)) := by
  have heq : (printedTable b t d modulus edges index).matrix =
      fun i j => matrix (placeEdges edges index)
        (fullSelector (2 ^ (t - 1)) (2 ^ b))
        (printedPairFieldWord b t d modulus)
        ((printedRowIndex v b t).symm i)
        ((printedColumnIndex b t d).symm j) := by
    funext i j
    exact tabulate_matrix _ i j
  rw [heq]
  exact Dalt_comap_equiv starter _
    (printedRowIndex v b t).symm (printedColumnIndex b t d).symm

theorem printedRowCount_pos {v : ℕ} (hv : 0 < v) (b t : ℕ) :
    0 < printedRowCount v b t := by
  unfold printedRowCount
  have hnonempty : Nonempty (Fin (2 ^ (t - 1)) → Fin (2 ^ b)) :=
    ⟨fun _ => ⟨0, by positivity⟩⟩
  have hc : 0 < Fintype.card (Fin (2 ^ (t - 1)) → Fin (2 ^ b)) :=
    Fintype.card_pos
  positivity

theorem printedColumnCount_pos (b t d : ℕ) :
    0 < printedColumnCount b t d := by
  unfold printedColumnCount
  positivity

/-- The public threshold is included in the encoded instance but not in
the matrix word supplied to an estimator. -/
noncomputable def printedInstance {v e : ℕ} (b t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (index : Fin e ↪ Fin (2 ^ b)) : Instance :=
  instanceOf (printedTable b t d modulus edges index) (2 * b + 4 * t + 2)

theorem printedInstance_valid {v e : ℕ} (hv : 0 < v)
    (b t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (index : Fin e ↪ Fin (2 ^ b)) :
    (printedInstance b t d modulus edges index).Valid :=
  instanceOf_valid _ _ (printedRowCount_pos hv b t)
    (printedColumnCount_pos b t d)

theorem printedInstance_Dalt {v e : ℕ} (b t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (index : Fin e ↪ Fin (2 ^ b)) (starter : Turn) :
    Dalt starter (ProtocolVerifier.tableGame
      (printedInstance b t d modulus edges index).rows
      (printedInstance b t d modulus edges index).cols
      (printedInstance b t d modulus edges index).table) =
      Dalt starter (matrix (placeEdges edges index)
        (fullSelector (2 ^ (t - 1)) (2 ^ b))
        (printedPairFieldWord b t d modulus)) := by
  rw [show ProtocolVerifier.tableGame
      (printedInstance b t d modulus edges index).rows
      (printedInstance b t d modulus edges index).cols
      (printedInstance b t d modulus edges index).table =
      (printedTable b t d modulus edges index).matrix by
        exact tableGame_eq_matrix _]
  exact printedTable_Dalt b t d modulus edges index starter

#print axioms CurrentAdditive.SmallBias.printedTable_Dalt
#print axioms CurrentAdditive.SmallBias.printedInstance_valid
#print axioms CurrentAdditive.SmallBias.printedInstance_Dalt

end CurrentAdditive.SmallBias
