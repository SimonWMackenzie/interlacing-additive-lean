import EthInapproximability.CurrentPaper.SourceClauseRowWriterOperands

/-!
# Persistent unary n/r transfers into the common row writer

The source words remain outside the arithmetic bank. The two preserving
broadcasts are inlined in one charged program; their target lists are fixed
finite syntax for a gate or unit call.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowWriterFanout

open Turing BitMachineEncoding
open scoped Classical

abbrev Stack (q : ℕ) := SourceClauseRowWriterOperands.Stack q

noncomputable def vertexProgram {q : ℕ} (nt : List (Stack q)) :=
  SourceClausePreservingBroadcast.program
    SourceClauseRowWriterOperands.vertex
    SourceClauseRowWriterOperands.scratch nt

noncomputable def rowProgram {q : ℕ} (rt : List (Stack q)) :=
  SourceClausePreservingBroadcast.program
    SourceClauseRowWriterOperands.rowIndex
    SourceClauseRowWriterOperands.scratch rt

noncomputable def program {q : ℕ} (nt rt : List (Stack q)) :=
  BitMachineRawSequence.program (vertexProgram nt) (rowProgram rt)
    SourceClausePreservingBroadcast.Label.scan ((), none) ((), none)

noncomputable def afterVertex {q : ℕ} (nt : List (Stack q))
    (n : ℕ) (S : Stack q → List Bool) :=
  SourceClausePreservingBroadcast.result
    SourceClauseRowWriterOperands.vertex
    SourceClauseRowWriterOperands.scratch nt (List.replicate n true) S

noncomputable def afterRow {q : ℕ} (nt rt : List (Stack q))
    (n r : ℕ) (S : Stack q → List Bool) :=
  SourceClausePreservingBroadcast.result
    SourceClauseRowWriterOperands.rowIndex
    SourceClauseRowWriterOperands.scratch rt (List.replicate r true)
    (afterVertex nt n S)

theorem run {q : ℕ} (nt rt : List (Stack q))
    (hnt : nt.Nodup) (hrt : rt.Nodup)
    (hnv : SourceClauseRowWriterOperands.vertex ∉ nt)
    (hns : SourceClauseRowWriterOperands.scratch ∉ nt)
    (hnr : SourceClauseRowWriterOperands.rowIndex ∉ nt)
    (hrv : SourceClauseRowWriterOperands.vertex ∉ rt)
    (hrr : SourceClauseRowWriterOperands.rowIndex ∉ rt)
    (hrs : SourceClauseRowWriterOperands.scratch ∉ rt)
    (n r : ℕ) (S : Stack q → List Bool)
    (hn : S SourceClauseRowWriterOperands.vertex = List.replicate n true)
    (hr : S SourceClauseRowWriterOperands.rowIndex = List.replicate r true)
    (hs : S SourceClauseRowWriterOperands.scratch = []) :
    ∃ T ≤ (2 * n + 3) + (2 * r + 3) + 1,
      ((advance (program nt rt))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          SourceClausePreservingBroadcast.Label.scan),
          (((), none), ((), none)), S⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (BitMachineRawSequence.Label
              SourceClausePreservingBroadcast.Label
              SourceClausePreservingBroadcast.Label)
            ((Unit × Option Bool) × (Unit × Option Bool))) =
        ⟨none, (((), none), ((), none)), afterRow nt rt n r S⟩ := by
  have hv := SourceClausePreservingBroadcast.run_halt
    SourceClauseRowWriterOperands.vertex
    SourceClauseRowWriterOperands.scratch nt
    (by simp [SourceClauseRowWriterOperands.vertex,
      SourceClauseRowWriterOperands.scratch])
    hnt hnv hns (List.replicate n true) S hn hs
  have hrow : afterVertex nt n S SourceClauseRowWriterOperands.rowIndex =
      List.replicate r true := by
    rw [afterVertex]
    exact (SourceClausePreservingBroadcast.other_preserved
      SourceClauseRowWriterOperands.vertex
      SourceClauseRowWriterOperands.scratch nt _ S
      SourceClauseRowWriterOperands.rowIndex
      (by simp [SourceClauseRowWriterOperands.rowIndex,
        SourceClauseRowWriterOperands.vertex])
      (by simp [SourceClauseRowWriterOperands.rowIndex,
        SourceClauseRowWriterOperands.scratch]) hnr).trans hr
  have htemp : afterVertex nt n S SourceClauseRowWriterOperands.scratch =
      [] := SourceClausePreservingBroadcast.temp_empty _ _ _ _ _
  have hw := SourceClausePreservingBroadcast.run_halt
    SourceClauseRowWriterOperands.rowIndex
    SourceClauseRowWriterOperands.scratch rt
    (by simp [SourceClauseRowWriterOperands.rowIndex,
      SourceClauseRowWriterOperands.scratch])
    hrt hrr hrs (List.replicate r true) (afterVertex nt n S) hrow htemp
  have hv' :
      ((advance (vertexProgram nt))^[2 * n + 3])
        (⟨some SourceClausePreservingBroadcast.Label.scan, ((), none), S⟩) =
      ⟨none, ((), none), afterVertex nt n S⟩ := by
    simpa [vertexProgram, afterVertex] using hv
  have hw' :
      ((advance (rowProgram rt))^[2 * r + 3])
        (⟨some SourceClausePreservingBroadcast.Label.scan, ((), none),
          afterVertex nt n S⟩) =
      ⟨none, ((), none), afterRow nt rt n r S⟩ := by
    simpa [rowProgram, afterRow] using hw
  simpa only [program] using BitMachineRawSequence.runs
    (vertexProgram nt) (rowProgram rt)
    SourceClausePreservingBroadcast.Label.scan
    SourceClausePreservingBroadcast.Label.scan
    ((), none) ((), none) ((), none) ((), none)
    S (afterVertex nt n S) (afterRow nt rt n r S)
    (2 * n + 3) (2 * r + 3) hv' hw'

theorem gate_wellformed {q : ℕ} :
    (SourceClauseRowWriterOperands.gateVertexTargets (q := q)).Nodup ∧
    (SourceClauseRowWriterOperands.gateRowTargets (q := q)).Nodup ∧
    SourceClauseRowWriterOperands.vertex ∉
      SourceClauseRowWriterOperands.gateVertexTargets (q := q) ∧
    SourceClauseRowWriterOperands.scratch ∉
      SourceClauseRowWriterOperands.gateVertexTargets (q := q) ∧
    SourceClauseRowWriterOperands.rowIndex ∉
      SourceClauseRowWriterOperands.gateVertexTargets (q := q) ∧
    SourceClauseRowWriterOperands.vertex ∉
      SourceClauseRowWriterOperands.gateRowTargets (q := q) ∧
    SourceClauseRowWriterOperands.rowIndex ∉
      SourceClauseRowWriterOperands.gateRowTargets (q := q) ∧
    SourceClauseRowWriterOperands.scratch ∉
      SourceClauseRowWriterOperands.gateRowTargets (q := q) := by
  simp [SourceClauseRowWriterOperands.gateVertexTargets,
    SourceClauseRowWriterOperands.gateRowTargets,
    SourceClauseRowWriterOperands.gateCell,
    SourceClauseRowWriterOperands.gateSlot,
    SourceClauseRowWriterOperands.gateOffset,
    SourceClauseRowWriterOperands.vertex,
    SourceClauseRowWriterOperands.rowIndex,
    SourceClauseRowWriterOperands.scratch,
    SourceClauseRowIndexedGate.gateEmbedding,
    SourceClauseRowGate.gateEmbedding,
    SourceClauseGateSlotAddress.offsetEmbedding]

theorem unit_wellformed {q : ℕ} :
    (SourceClauseRowWriterOperands.unitVertexTargets (q := q)).Nodup ∧
    (SourceClauseRowWriterOperands.unitRowTargets (q := q)).Nodup ∧
    SourceClauseRowWriterOperands.vertex ∉
      SourceClauseRowWriterOperands.unitVertexTargets (q := q) ∧
    SourceClauseRowWriterOperands.scratch ∉
      SourceClauseRowWriterOperands.unitVertexTargets (q := q) ∧
    SourceClauseRowWriterOperands.rowIndex ∉
      SourceClauseRowWriterOperands.unitVertexTargets (q := q) ∧
    SourceClauseRowWriterOperands.vertex ∉
      SourceClauseRowWriterOperands.unitRowTargets (q := q) ∧
    SourceClauseRowWriterOperands.rowIndex ∉
      SourceClauseRowWriterOperands.unitRowTargets (q := q) ∧
    SourceClauseRowWriterOperands.scratch ∉
      SourceClauseRowWriterOperands.unitRowTargets (q := q) := by
  simp [SourceClauseRowWriterOperands.unitVertexTargets,
    SourceClauseRowWriterOperands.unitRowTargets,
    SourceClauseRowWriterOperands.unitCell,
    SourceClauseRowWriterOperands.unitAddress,
    SourceClauseRowWriterOperands.vertex,
    SourceClauseRowWriterOperands.rowIndex,
    SourceClauseRowWriterOperands.scratch,
    SourceClauseRowUnitAddress.slotEmbedding,
    SourceClauseRowUnitAddress.offsetEmbedding]

theorem gate_run {q : ℕ} (n r : ℕ) (S : Stack q → List Bool)
    (hn : S SourceClauseRowWriterOperands.vertex = List.replicate n true)
    (hr : S SourceClauseRowWriterOperands.rowIndex = List.replicate r true)
    (hs : S SourceClauseRowWriterOperands.scratch = []) :
    ∃ T ≤ (2 * n + 3) + (2 * r + 3) + 1,
      ((advance (program SourceClauseRowWriterOperands.gateVertexTargets
        SourceClauseRowWriterOperands.gateRowTargets))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          SourceClausePreservingBroadcast.Label.scan),
          (((), none), ((), none)), S⟩) =
        ⟨none, (((), none), ((), none)),
          afterRow SourceClauseRowWriterOperands.gateVertexTargets
            SourceClauseRowWriterOperands.gateRowTargets n r S⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := gate_wellformed (q := q)
  exact run _ _ h1 h2 h3 h4 h5 h6 h7 h8 n r S hn hr hs

theorem unit_run {q : ℕ} (n r : ℕ) (S : Stack q → List Bool)
    (hn : S SourceClauseRowWriterOperands.vertex = List.replicate n true)
    (hr : S SourceClauseRowWriterOperands.rowIndex = List.replicate r true)
    (hs : S SourceClauseRowWriterOperands.scratch = []) :
    ∃ T ≤ (2 * n + 3) + (2 * r + 3) + 1,
      ((advance (program SourceClauseRowWriterOperands.unitVertexTargets
        SourceClauseRowWriterOperands.unitRowTargets))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          SourceClausePreservingBroadcast.Label.scan),
          (((), none), ((), none)), S⟩) =
        ⟨none, (((), none), ((), none)),
          afterRow SourceClauseRowWriterOperands.unitVertexTargets
            SourceClauseRowWriterOperands.unitRowTargets n r S⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := unit_wellformed (q := q)
  exact run _ _ h1 h2 h3 h4 h5 h6 h7 h8 n r S hn hr hs

theorem vertex_target_written {q : ℕ} (nt rt : List (Stack q))
    (hnv : SourceClauseRowWriterOperands.vertex ∉ nt)
    (hns : SourceClauseRowWriterOperands.scratch ∉ nt)
    (n r : ℕ) (S : Stack q → List Bool)
    (x : Stack q) (hx : x ∈ nt) (hxr : x ∉ rt)
    (hr : x ≠ SourceClauseRowWriterOperands.rowIndex)
    (hs : x ≠ SourceClauseRowWriterOperands.scratch) :
    afterRow nt rt n r S x = List.replicate n true ++ S x := by
  rw [afterRow, SourceClausePreservingBroadcast.other_preserved
    SourceClauseRowWriterOperands.rowIndex
    SourceClauseRowWriterOperands.scratch rt _ (afterVertex nt n S)
    x hr hs hxr]
  exact SourceClausePreservingBroadcast.target_written
    SourceClauseRowWriterOperands.vertex
    SourceClauseRowWriterOperands.scratch nt hns hnv
    (by simp [SourceClauseRowWriterOperands.vertex,
      SourceClauseRowWriterOperands.scratch])
    (List.replicate n true) S x hx

theorem row_target_written {q : ℕ} (nt rt : List (Stack q))
    (hrr : SourceClauseRowWriterOperands.rowIndex ∉ rt)
    (hrs : SourceClauseRowWriterOperands.scratch ∉ rt)
    (n r : ℕ) (S : Stack q → List Bool)
    (x : Stack q) (hx : x ∈ rt) (hxn : x ∉ nt)
    (hv : x ≠ SourceClauseRowWriterOperands.vertex)
    (hs : x ≠ SourceClauseRowWriterOperands.scratch) :
    afterRow nt rt n r S x = List.replicate r true ++ S x := by
  rw [afterRow, SourceClausePreservingBroadcast.target_written
    SourceClauseRowWriterOperands.rowIndex
    SourceClauseRowWriterOperands.scratch rt hrs hrr
    (by simp [SourceClauseRowWriterOperands.rowIndex,
      SourceClauseRowWriterOperands.scratch])
    (List.replicate r true) (afterVertex nt n S) x hx]
  congr 1
  exact SourceClausePreservingBroadcast.other_preserved
    SourceClauseRowWriterOperands.vertex
    SourceClauseRowWriterOperands.scratch nt _ S x hv hs hxn

end EthInapproximability.CurrentPaper.SourceClauseRowWriterFanout
