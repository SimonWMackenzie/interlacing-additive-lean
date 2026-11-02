import EthInapproximability.CurrentPaper.MatrixTableRuntime
import EthInapproximability.CurrentPaper.MatrixScalarTableSequence
import EthInapproximability.CurrentPaper.ExecutableExactReduction
import EthInapproximability.CurrentPaper.SourceGraphVectorPayload

/-! # Physical truth-table writer for the exact graph instance

This instantiates the fixed finite table writer at the executable binary-field
sampled families and five-copy graph vectors. Its three Boolean arrays are explicit
inputs. The scalar-plus-writer theorem below initializes the scalar bank
physically from unary inputs. Producing the three arrays from encoded graph
bits and writing the binary instance header remain separate operational
stages; they are not assigned zero cost.
-/

namespace EthInapproximability.CurrentPaper.MatrixExactGraphTable

open Turing BitMachineEncoding
open MatrixTableRuntime MatrixTableWriter
open ExactEncodedReduction (rowCount columnCount)
open ExactConstruction MatrixMaterialization
open ExactParameters

def graphBank (s : ℕ) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) : Fin 51 → List Bool :=
  persistentBank (firstExponent s) (dimension s) (firstListSize s)
    (secondListSize s) (ExecutableExactReduction.payload s e)

/-- In the 51-cell writer bank, cell 30 is the source-vector payload. This
ties the graph decoder's copy-major Boolean list to the table callback. -/
theorem graphBank_source (s : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid) :
    graphBank s (EncodedGraph.endpoints g hg) 30 =
      SourceGraphVectorPayload.exactBits g hg (dimension s) := by
  rfl

/-- The table phase emits precisely the table of the encoded exact reduction,
with the writer's physical cell bank and loop counters restored. -/
theorem write_graphTable (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) (output : List Bool) :
    ∃ t ≤ MatrixTableRuntimeBounds.bound (firstExponent s)
      (dimension s) (firstListSize s) (secondListSize s) (5 * n), ∃ state,
      MatrixTableWriter.run entryProgram MatrixEntryProgram.start MatrixEntryProgram.initial t
        (MatrixTableWriter.cfg (some (.inr (.copy .rows)))
          (MatrixEntryProgram.initial, none)
          (MatrixTableWriter.ready (graphBank s e) (rowCount s n)
            (columnCount s) 0 0 0 0 [] output)) =
      MatrixTableWriter.cfg none state
        (MatrixTableWriter.ready (graphBank s e) (rowCount s n)
          (columnCount s) 0 0 0 0 []
          (ExecutableExactReduction.literalTable s hs e ++ output)) := by
  have h := MatrixTableRuntime.write_bitTable
    (ExecutableExactReduction.alphabet_valid s hs)
    (ExecutableExactReduction.firstFamily s)
    (ExecutableExactReduction.secondFamily s) (sourceVectors (dimension s) e)
    (sourceVectors_cap (dimension s) e) output
  simpa only [graphBank, ExecutableExactReduction.literalTable,
    ExecutableExactReduction.payload, rowCount, columnCount]
    using h

/-- Specialization to an actual decoded graph. The output table is the table
field of its executable encoded communication instance; the source cell is
the graph's five-copy row-major payload by `graphBank_source`. -/
theorem write_encodedGraphTable (s : ℕ) (hs : 2 ^ 21 ≤ s)
    (g : EncodedGraph.Graph) (hg : g.Valid) (output : List Bool) :
    ∃ t ≤ MatrixTableRuntimeBounds.bound (firstExponent s)
      (dimension s) (firstListSize s) (secondListSize s) (5 * g.vertices), ∃ state,
      MatrixTableWriter.run entryProgram MatrixEntryProgram.start MatrixEntryProgram.initial t
        (MatrixTableWriter.cfg (some (.inr (.copy .rows)))
          (MatrixEntryProgram.initial, none)
          (MatrixTableWriter.ready (graphBank s (EncodedGraph.endpoints g hg))
            (rowCount s g.vertices) (columnCount s) 0 0 0 0 [] output)) =
      MatrixTableWriter.cfg none state
        (MatrixTableWriter.ready (graphBank s (EncodedGraph.endpoints g hg))
          (rowCount s g.vertices) (columnCount s) 0 0 0 0 []
          ((ExecutableExactReduction.instanceAt s hs (EncodedGraph.endpoints g hg)).table ++
            output)) := by
  simpa only [ExecutableExactReduction.instanceAt] using
    write_graphTable s hs (EncodedGraph.endpoints g hg) output

/-- Scalar construction and the entire matrix table are now one physical
program, starting with unary inputs and literal arrays rather than a
precomputed entry bank. Array generation and binary headers remain separate. -/
theorem write_graphTable_from_scalars (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) :
    ∃ t ≤ 200 * (2^(firstExponent s) + firstExponent s + dimension s +
        firstListSize s + secondListSize s + 5*n +
        (dimension s * firstListSize s)^4 + 1) +
        MatrixTableRuntimeBounds.bound (firstExponent s) (dimension s)
          (firstListSize s) (secondListSize s) (5*n) + 1,
      ∃ state,
        ((advance MatrixScalarTableSequence.program)^[t])
          (⟨some (.inl (.inl (.inr false))),
            (MatrixScalarParameters.idle, MatrixScalarTableSequence.writerInitial),
            MatrixScalarWriterFrame.rawInput (firstExponent s) (dimension s)
              (firstListSize s) (secondListSize s) (5*n)
              (ExecutableExactReduction.payload s e)⟩ :
              TM2.Cfg (fun _ : MatrixScalarTableSequence.Stack => Bool) _ _) =
          ⟨none, (MatrixScalarParameters.idle, state),
            MatrixScalarTableSequence.finalFrame (firstExponent s) (dimension s)
              (firstListSize s) (secondListSize s) (5*n)
              (ExecutableExactReduction.payload s e)
              (ExecutableExactReduction.literalTable s hs e)⟩ := by
  simpa only [ExecutableExactReduction.literalTable,
    ExecutableExactReduction.payload] using
    MatrixScalarTableSequence.scalar_write_run
      (ExecutableExactReduction.alphabet_valid s hs)
      (ExecutableExactReduction.firstFamily s)
      (ExecutableExactReduction.secondFamily s)
      (sourceVectors (dimension s) e) (sourceVectors_cap (dimension s) e)

/-- Actual decoded-graph specialization of the scalar-plus-table machine.
The table field agrees with the executable instance, while the table's
three arrays are still separately supplied physical inputs. -/
theorem write_encodedGraphTable_from_scalars (s : ℕ) (hs : 2 ^ 21 ≤ s)
    (g : EncodedGraph.Graph) (hg : g.Valid) :
    ∃ t ≤ 200 * (2^(firstExponent s) + firstExponent s + dimension s +
        firstListSize s + secondListSize s + 5*g.vertices +
        (dimension s * firstListSize s)^4 + 1) +
        MatrixTableRuntimeBounds.bound (firstExponent s) (dimension s)
          (firstListSize s) (secondListSize s) (5*g.vertices) + 1,
      ∃ state,
        ((advance MatrixScalarTableSequence.program)^[t])
          (⟨some (.inl (.inl (.inr false))),
            (MatrixScalarParameters.idle, MatrixScalarTableSequence.writerInitial),
            MatrixScalarWriterFrame.rawInput (firstExponent s) (dimension s)
              (firstListSize s) (secondListSize s) (5*g.vertices)
              (ExecutableExactReduction.payload s (EncodedGraph.endpoints g hg))⟩ :
              TM2.Cfg (fun _ : MatrixScalarTableSequence.Stack => Bool) _ _) =
          ⟨none, (MatrixScalarParameters.idle, state),
            MatrixScalarTableSequence.finalFrame (firstExponent s) (dimension s)
              (firstListSize s) (secondListSize s) (5*g.vertices)
              (ExecutableExactReduction.payload s (EncodedGraph.endpoints g hg))
              (ExecutableExactReduction.instanceAt s hs
                (EncodedGraph.endpoints g hg)).table⟩ := by
  simpa only [ExecutableExactReduction.instanceAt] using
    write_graphTable_from_scalars s hs (EncodedGraph.endpoints g hg)

end EthInapproximability.CurrentPaper.MatrixExactGraphTable
