import CurrentAdditive.V38SourceBridge
import CurrentAdditive.SmallBiasEncodedTable

/-!
Private v38 semantic serialization bridge. The row and column enumerations are
the selected dimensions. Every bit is read from the same literal v38 matrix.
This `tabulate` is a finite list construction, not yet a proved all-input
polynomial-time bit-machine for the complete table.
-/

namespace CurrentAdditive.V38Encoded

open CurrentAdditive.SmallBias
open CurrentAdditive.V38Source
open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol
open Paper2.EncodedSelectedOutput
open Paper2.YaoMaterialization
open CurrentAdditive.FiniteFieldConstructor
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

noncomputable def printedTable {v e : ℕ} (b t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (index : Fin e ↪ Fin (2 ^ b)) :
    SerializedTable (SmallBias.printedRowCount v b t)
      (SmallBias.printedColumnCount b t d) :=
  tabulate fun i j =>
    matrixV38 (placeEdges edges index)
      (fullSelector (2 ^ (t - 1)) (2 ^ b))
      (v38PrintedPairWord b t d modulus)
      ((SmallBias.printedRowIndex v b t).symm i)
      ((SmallBias.printedColumnIndex b t d).symm j)

theorem printedTable_Dalt {v e : ℕ} (b t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (index : Fin e ↪ Fin (2 ^ b)) (starter : Turn) :
    Dalt starter (printedTable b t d modulus edges index).matrix =
      Dalt starter (matrixV38 (placeEdges edges index)
        (fullSelector (2 ^ (t - 1)) (2 ^ b))
        (v38PrintedPairWord b t d modulus)) := by
  have heq : (printedTable b t d modulus edges index).matrix =
      fun i j => matrixV38 (placeEdges edges index)
        (fullSelector (2 ^ (t - 1)) (2 ^ b))
        (v38PrintedPairWord b t d modulus)
        ((SmallBias.printedRowIndex v b t).symm i)
        ((SmallBias.printedColumnIndex b t d).symm j) := by
    funext i j
    exact tabulate_matrix _ i j
  rw [heq]
  exact Dalt_comap_equiv starter _
    (SmallBias.printedRowIndex v b t).symm
    (SmallBias.printedColumnIndex b t d).symm

noncomputable def printedInstance {v e : ℕ} (b t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (index : Fin e ↪ Fin (2 ^ b)) : Instance :=
  instanceOf (printedTable b t d modulus edges index) (2 * b + 4 * t + 2)

theorem printedInstance_valid {v e : ℕ} (hv : 0 < v)
    (b t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (index : Fin e ↪ Fin (2 ^ b)) :
    (printedInstance b t d modulus edges index).Valid :=
  instanceOf_valid _ _ (SmallBias.printedRowCount_pos hv b t)
    (SmallBias.printedColumnCount_pos b t d)

theorem printedInstance_Dalt {v e : ℕ} (b t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (index : Fin e ↪ Fin (2 ^ b)) (starter : Turn) :
    Dalt starter (ProtocolVerifier.tableGame
      (printedInstance b t d modulus edges index).rows
      (printedInstance b t d modulus edges index).cols
      (printedInstance b t d modulus edges index).table) =
      Dalt starter (matrixV38 (placeEdges edges index)
        (fullSelector (2 ^ (t - 1)) (2 ^ b))
        (v38PrintedPairWord b t d modulus)) := by
  rw [show ProtocolVerifier.tableGame
      (printedInstance b t d modulus edges index).rows
      (printedInstance b t d modulus edges index).cols
      (printedInstance b t d modulus edges index).table =
      (printedTable b t d modulus edges index).matrix by
        exact tableGame_eq_matrix _]
  exact printedTable_Dalt b t d modulus edges index starter

def edgeBits (e : ℕ) : ℕ := Nat.clog 2 e

theorem edgeCount_le_capacity (e : ℕ) : e ≤ 2 ^ edgeBits e := by
  exact Nat.le_pow_clog (by decide) e

def sourceIndex {t : ℕ} (G : GLSourceInput t) (input : List Bool) :
    Fin (selectedSource G input).2.1 ↪
      Fin (2 ^ edgeBits (selectedSource G input).2.1) :=
  Fin.castLEEmb (edgeCount_le_capacity _)

/-- Exact source-dependent selected matrix, with its public modulus and
array list still chosen without inspecting the YES/NO promise. -/
theorem selected_printed_table_costs {t : ℕ} (G : GLSourceInput t)
    (input : List Bool) (ht : 4 ≤ t) :
    let src := selectedSource G input
    let b := edgeBits src.2.1
    ∃ output : List (ℕ × ℕ × List Bool), ∃ modulus : ℕ,
      TrialSearch.makeList (v38FieldDegree b t) (v38PositionCount b t) = some output ∧
      TrialSearch.firstPassing (v38FieldDegree b t) = some modulus ∧
      output = StreamingPrinter.labelledWords (v38FieldDegree b t)
        modulus (v38PositionCount b t) ∧
      (input ∈ G.L →
        Dalt .alice (printedTable b t (v38FieldDegree b t) modulus
          src.2.2 (sourceIndex G input)).matrix ≤ 2 * b + 4 * t + 2) ∧
      (input ∉ G.L →
        (2 * b + 4 * t + 2) + 2 * t - 8 ≤
          Dalt .alice (printedTable b t (v38FieldDegree b t) modulus
            src.2.2 (sourceIndex G input)).matrix) := by
  dsimp only
  let src := selectedSource G input
  let b := edgeBits src.2.1
  obtain ⟨output, modulus, houtput, hmodulus, hout, hyes, hno⟩ :=
    v38_public_printed_matrix_yes_no b t ht src.2.2 (sourceIndex G input)
  refine ⟨output, modulus, houtput, hmodulus, hout, ?_, ?_⟩
  · intro hy
    rw [printedTable_Dalt]
    obtain ⟨colour, hbal⟩ := selectedSource_yes G input hy
    exact hyes colour hbal
  · intro hn
    rw [printedTable_Dalt]
    have hcol : ∀ colour : Fin src.1 → Fin (2 ^ (2 ^ t)),
        ∃ e c, ∀ i, colour (src.2.2 e i) = c := by
      simpa only [src, colourCount] using selectedSource_no G input hn
    exact hno hcol

#print axioms printedTable_Dalt
#print axioms printedInstance_valid
#print axioms printedInstance_Dalt
#print axioms selected_printed_table_costs

end CurrentAdditive.V38Encoded
