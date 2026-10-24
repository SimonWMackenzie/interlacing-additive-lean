import EthInapproximability.CurrentPaper.VectorsCellRun

/-!
# Segment 1: the `MatrixTableWriter.EntryRuns` instance and the physical
# `GraphVectors.vectors G s` row-major table

Lane owner:b-stage4-entry-program-3 (Paper B, unit 2, map item 3).

* `cellValue_eq`: the bit computed by the thirteen phases is
  `EntryVectorsFormula.cellRule` when `D = |V| + B` and `M4 = 4 s m`.
* `cellBound_le`: one public per-cell clock, uniform over all indices below
  the table dimensions.
* `entry_runs`: the admitted local contract `MatrixTableWriter.EntryRuns` for
  the literal fixed `EntryVectorsCell.program` on the fixed bank.
* `vectors_table`: the admitted row-major writer `MatrixTableWriter.program`
  with THIS entry program writes exactly
  `MatrixMaterialization.rowMajor (GraphVectors.vectors G s)` in front of an
  arbitrary old output, restoring the bank and both dimension counters
  (`write_rowMajor` with `EntryVectorsFormula.vectors_formula`).
-/

namespace EthInapproximability.CurrentPaper.VectorsTable

open Turing BitMachineEncoding
open EthInapproximability.CurrentPaper.EntryVectorsCell
open EthInapproximability.CurrentPaper.VectorsCellRun
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab

noncomputable section

theorem cellValue_eq (edges : List (ℕ × ℕ)) (s nV B m x y : ℕ) :
    cellValue edges (nV + B) nV m (4 * s * m) x y =
      EntryVectorsFormula.cellRule edges s nV B m x y := by
  unfold cellValue comb EntryUnaryCompare.verdict EntryVectorsFormula.cellRule
  by_cases h1 : y < 4 * s * m <;> by_cases h2 : y / m = x / (nV + B) <;>
    by_cases h3 : x % (nV + B) < nV <;> simp [h1, h2, h3]

/-- The public per-cell clock (uniform in the indices below `X`, `Y`). -/
def vectorsT (X Y D nV m M4 L Ed : ℕ) : ℕ :=
  20 * (X + Y + m + D + M4 + nV) + 16 * (L + 1) * (Ed + 1) + 50

theorem cellBound_le (edges : List (ℕ × ℕ)) (D nV m M4 x y X Y : ℕ)
    (hx : x ≤ X) (hy : y ≤ Y) :
    cellBound edges D nV m M4 x y ≤
      vectorsT X Y D nV m M4 (SourceGraphPayloadMachine.endpointStream edges).length
        edges.length := by
  have d1 := MatrixUnaryDivision.totalTime_bound y m
  have d2 := MatrixUnaryDivision.totalTime_bound x D
  have e1 : y / m ≤ y := Nat.div_le_self y m
  have e2 : x / D ≤ x := Nat.div_le_self x D
  have e3 : x % D ≤ x := Nat.mod_le x D
  have e4 : y % m ≤ y := Nat.mod_le y m
  have f1 : max y M4 ≤ y + M4 := max_le (by omega) (by omega)
  have f2 : max (y / m) (x / D) ≤ y + x := max_le (by omega) (by omega)
  have f3 : max (x % D) nV ≤ x + nV := max_le (by omega) (by omega)
  unfold cellBound vectorsT
  generalize 16 * ((SourceGraphPayloadMachine.endpointStream edges).length + 1) *
    (edges.length + 1) = P
  omega

theorem entry_runs (edges : List (ℕ × ℕ)) (D nV m M4 r c : ℕ) :
    MatrixTableWriter.EntryRuns program
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) initControl
      (cellBank edges D nV m M4) r c
      (vectorsT r c D nV m M4 (SourceGraphPayloadMachine.endpointStream edges).length
        edges.length)
      (cellValue edges D nV m M4) := by
  intro x hx y hy
  obtain ⟨t, ht, v, h⟩ := cell_run edges D nV m M4 x y
  exact ⟨t, ht.trans (cellBound_le edges D nV m M4 x y r c hx.le hy.le), v, h⟩

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The fixed bank of the vectors cell program for the graph `G` and `s`:
endpoint stream of `serializeGraph G`, unary `|V| + (s-3)`, `|V|`, `|E|`,
`4 s |E|`, all other cells blank. -/
def graphBank (G : EndpointGraph V E) (s : ℕ) : Fin 25 → List Bool :=
  cellBank (EncodedETHSource.serializeGraph G).edges (Fintype.card V + (s - 3))
    (Fintype.card V) (Fintype.card E) (4 * s * Fintype.card E)

/-- The table's public per-cell clock. -/
def tableT (G : EndpointGraph V E) (s : ℕ) : ℕ :=
  vectorsT (GraphVectors.vertexCount V s + GraphVectors.auxiliaryCount s) (q2 G s)
    (Fintype.card V + (s - 3)) (Fintype.card V) (Fintype.card E) (4 * s * Fintype.card E)
    (SourceGraphPayloadMachine.endpointStream (EncodedETHSource.serializeGraph G).edges).length
    (EncodedETHSource.serializeGraph G).edges.length

theorem graph_entry_runs (G : EndpointGraph V E) (s : ℕ) :
    MatrixTableWriter.EntryRuns program
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) initControl
      (graphBank G s) (GraphVectors.vertexCount V s + GraphVectors.auxiliaryCount s)
      (q2 G s) (tableT G s)
      (EntryVectorsFormula.cellRule (EncodedETHSource.serializeGraph G).edges s
        (Fintype.card V) (s - 3) (Fintype.card E)) := by
  have h := entry_runs (EncodedETHSource.serializeGraph G).edges
    (Fintype.card V + (s - 3)) (Fintype.card V) (Fintype.card E) (4 * s * Fintype.card E)
    (GraphVectors.vertexCount V s + GraphVectors.auxiliaryCount s) (q2 G s)
  have hv : cellValue (EncodedETHSource.serializeGraph G).edges
      (Fintype.card V + (s - 3)) (Fintype.card V) (Fintype.card E)
      (4 * s * Fintype.card E) =
      EntryVectorsFormula.cellRule (EncodedETHSource.serializeGraph G).edges s
        (Fintype.card V) (s - 3) (Fintype.card E) := by
    funext x y
    exact cellValue_eq _ s _ _ _ x y
  rw [hv] at h
  exact h

/-- The physical vectors table: the admitted row-major writer running the
literal fixed cell program writes `rowMajor (GraphVectors.vectors G s)`. -/
theorem vectors_table (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ∃ t ≤ MatrixTableWriter.writerBound
        (GraphVectors.vertexCount V s + GraphVectors.auxiliaryCount s) (q2 G s) (tableT G s),
      ∃ v,
        MatrixTableWriter.run program
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) initControl t
          (MatrixTableWriter.cfg (some (.inr (.copy .rows))) (initControl, none)
            (MatrixTableWriter.ready (graphBank G s)
              (GraphVectors.vertexCount V s + GraphVectors.auxiliaryCount s) (q2 G s)
              0 0 0 0 [] output)) =
        MatrixTableWriter.cfg none v
          (MatrixTableWriter.ready (graphBank G s)
            (GraphVectors.vertexCount V s + GraphVectors.auxiliaryCount s) (q2 G s)
            0 0 0 0 [] (MatrixMaterialization.rowMajor (GraphVectors.vectors G s) ++ output)) :=
  MatrixTableWriter.write_rowMajor program
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) initControl
    (graphBank G s) _ _ (tableT G s) _ (GraphVectors.vectors G s)
    (fun x y => (EntryVectorsFormula.vectors_formula G s x y).symm)
    (graph_entry_runs G s) output

#print axioms cellValue_eq
#print axioms cellBound_le
#print axioms entry_runs
#print axioms graph_entry_runs
#print axioms vectors_table

end
end EthInapproximability.CurrentPaper.VectorsTable
