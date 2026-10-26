import EthInapproximability.CurrentPaper.SourceClauseRowWriterBlank

/-!
# Charged operand staging for one row gate or unit writer

First preserve-copy the persistent unary n/r words into arithmetic inputs.
Then physically push every fixed tuple/position constant into the remaining
scratch inputs. This program does not emit a clause; it establishes the
operand bank needed by a later inlined clause writer.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowWriterStage

open Turing BitMachineEncoding
open scoped Classical

abbrev Stack (q : ℕ) := SourceClauseRowWriterOperands.Stack q
abbrev FanoutLabel := BitMachineRawSequence.Label
  SourceClausePreservingBroadcast.Label SourceClausePreservingBroadcast.Label
abbrev FanoutControl :=
  (Unit × Option Bool) × (Unit × Option Bool)

noncomputable def gateProgram {q : ℕ} (a k s t w : ℕ) :
    BitMachineRawSequence.Label FanoutLabel
      (SourceClauseFixedBatch.Label
        (SourceClauseRowWriterOperands.gateSizes a q k s t w)) →
    TM2.Stmt (fun _ : Stack q => Bool)
      (BitMachineRawSequence.Label FanoutLabel
        (SourceClauseFixedBatch.Label
          (SourceClauseRowWriterOperands.gateSizes a q k s t w)))
      (FanoutControl × Unit) :=
  BitMachineRawSequence.program
    (SourceClauseRowWriterFanout.program
      (SourceClauseRowWriterOperands.gateVertexTargets (q := q))
      (SourceClauseRowWriterOperands.gateRowTargets (q := q)))
    (SourceClauseFixedBatch.program (SourceClauseRowWriterOperands.gateConstants (q := q))
      (SourceClauseRowWriterOperands.gateSizes a q k s t w))
    (SourceClauseFixedBatch.labelAt
      (SourceClauseRowWriterOperands.gateSizes a q k s t w) 0)
    (((), none), ((), none)) ()

noncomputable def unitProgram {q : ℕ} (a k w ell : ℕ) :
    BitMachineRawSequence.Label FanoutLabel
      (SourceClauseFixedBatch.Label
        (SourceClauseRowWriterOperands.unitSizes a q k w ell)) →
    TM2.Stmt (fun _ : Stack q => Bool)
      (BitMachineRawSequence.Label FanoutLabel
        (SourceClauseFixedBatch.Label
          (SourceClauseRowWriterOperands.unitSizes a q k w ell)))
      (FanoutControl × Unit) :=
  BitMachineRawSequence.program
    (SourceClauseRowWriterFanout.program
      (SourceClauseRowWriterOperands.unitVertexTargets (q := q))
      (SourceClauseRowWriterOperands.unitRowTargets (q := q)))
    (SourceClauseFixedBatch.program (SourceClauseRowWriterOperands.unitConstants (q := q))
      (SourceClauseRowWriterOperands.unitSizes a q k w ell))
    (SourceClauseFixedBatch.labelAt
      (SourceClauseRowWriterOperands.unitSizes a q k w ell) 0)
    (((), none), ((), none)) ()

noncomputable def gateFinal {q : ℕ} (n r a k s t w : ℕ)
    (S : Stack q → List Bool) : Stack q → List Bool :=
  SourceClauseRowWriterOperands.gateFixedBank a k s t w
    (SourceClauseRowWriterFanout.afterRow
      SourceClauseRowWriterOperands.gateVertexTargets
      SourceClauseRowWriterOperands.gateRowTargets n r S)

noncomputable def unitFinal {q : ℕ} (n r a k w ell : ℕ)
    (S : Stack q → List Bool) : Stack q → List Bool :=
  SourceClauseRowWriterOperands.unitFixedBank a k w ell
    (SourceClauseRowWriterFanout.afterRow
      SourceClauseRowWriterOperands.unitVertexTargets
      SourceClauseRowWriterOperands.unitRowTargets n r S)

theorem gate_run {q : ℕ} (n r a k s t w : ℕ)
    (S : Stack q → List Bool)
    (hn : S SourceClauseRowWriterOperands.vertex = List.replicate n true)
    (hr : S SourceClauseRowWriterOperands.rowIndex = List.replicate r true)
    (hs : S SourceClauseRowWriterOperands.scratch = []) :
    ∃ T ≤ ((2 * n + 3) + (2 * r + 3) + 1) +
      (SourceClauseFixedBatch.costPrefix
        (SourceClauseRowWriterOperands.gateSizes a q k s t w) 8 + 1) + 1,
      ((advance (gateProgram a k s t w))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            SourceClausePreservingBroadcast.Label.scan)),
          ((((), none), ((), none)), ()), S⟩) =
        ⟨none, ((((), none), ((), none)), ()),
          gateFinal n r a k s t w S⟩ := by
  obtain ⟨tf, htf, hf⟩ := SourceClauseRowWriterFanout.gate_run
    n r S hn hr hs
  have hb := SourceClauseRowWriterOperands.gate_fixed_run a k s t w
    (SourceClauseRowWriterFanout.afterRow
      SourceClauseRowWriterOperands.gateVertexTargets
      SourceClauseRowWriterOperands.gateRowTargets n r S)
  obtain ⟨T, hT, hrun⟩ := BitMachineRawSequence.runs
    (SourceClauseRowWriterFanout.program
      SourceClauseRowWriterOperands.gateVertexTargets
      SourceClauseRowWriterOperands.gateRowTargets)
    (SourceClauseFixedBatch.program SourceClauseRowWriterOperands.gateConstants
      (SourceClauseRowWriterOperands.gateSizes a q k s t w))
    (BitMachineRawSequence.leftLabel
      SourceClausePreservingBroadcast.Label.scan)
    (SourceClauseFixedBatch.labelAt
      (SourceClauseRowWriterOperands.gateSizes a q k s t w) 0)
    (((), none), ((), none)) (((), none), ((), none)) () ()
    S (SourceClauseRowWriterFanout.afterRow
      SourceClauseRowWriterOperands.gateVertexTargets
      SourceClauseRowWriterOperands.gateRowTargets n r S)
    (gateFinal n r a k s t w S)
    tf (SourceClauseFixedBatch.costPrefix
      (SourceClauseRowWriterOperands.gateSizes a q k s t w) 8 + 1)
    hf hb
  exact ⟨T, by omega, hrun⟩

theorem unit_run {q : ℕ} (n r a k w ell : ℕ)
    (S : Stack q → List Bool)
    (hn : S SourceClauseRowWriterOperands.vertex = List.replicate n true)
    (hr : S SourceClauseRowWriterOperands.rowIndex = List.replicate r true)
    (hs : S SourceClauseRowWriterOperands.scratch = []) :
    ∃ T ≤ ((2 * n + 3) + (2 * r + 3) + 1) +
      (SourceClauseFixedBatch.costPrefix
        (SourceClauseRowWriterOperands.unitSizes a q k w ell) 6 + 1) + 1,
      ((advance (unitProgram a k w ell))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            SourceClausePreservingBroadcast.Label.scan)),
          ((((), none), ((), none)), ()), S⟩) =
        ⟨none, ((((), none), ((), none)), ()),
          unitFinal n r a k w ell S⟩ := by
  obtain ⟨tf, htf, hf⟩ := SourceClauseRowWriterFanout.unit_run
    n r S hn hr hs
  have hb := SourceClauseRowWriterOperands.unit_fixed_run a k w ell
    (SourceClauseRowWriterFanout.afterRow
      SourceClauseRowWriterOperands.unitVertexTargets
      SourceClauseRowWriterOperands.unitRowTargets n r S)
  obtain ⟨T, hT, hrun⟩ := BitMachineRawSequence.runs
    (SourceClauseRowWriterFanout.program
      SourceClauseRowWriterOperands.unitVertexTargets
      SourceClauseRowWriterOperands.unitRowTargets)
    (SourceClauseFixedBatch.program SourceClauseRowWriterOperands.unitConstants
      (SourceClauseRowWriterOperands.unitSizes a q k w ell))
    (BitMachineRawSequence.leftLabel
      SourceClausePreservingBroadcast.Label.scan)
    (SourceClauseFixedBatch.labelAt
      (SourceClauseRowWriterOperands.unitSizes a q k w ell) 0)
    (((), none), ((), none)) (((), none), ((), none)) () ()
    S (SourceClauseRowWriterFanout.afterRow
      SourceClauseRowWriterOperands.unitVertexTargets
      SourceClauseRowWriterOperands.unitRowTargets n r S)
    (unitFinal n r a k w ell S)
    tf (SourceClauseFixedBatch.costPrefix
      (SourceClauseRowWriterOperands.unitSizes a q k w ell) 6 + 1)
    hf hb
  exact ⟨T, by omega, hrun⟩

end EthInapproximability.CurrentPaper.SourceClauseRowWriterStage
