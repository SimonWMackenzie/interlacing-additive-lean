import EthInapproximability.CurrentPaper.SourceClauseRowWriterInitial

/-!
# Physical duplicate query input for the row-derived gate

The frozen row-gate initial bank contains a unary copy of the checked query
word in addition to the checked row cell from which its program reads. This
charged broadcast makes the duplicate from that very row cell. Its source is
restored; no vertex index is supplied as an algorithmic oracle.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowWriterQueryEcho

open Turing BitMachineEncoding
open scoped Classical

abbrev Stack (q : ℕ) := SourceClauseRowWriterOperands.Stack q

noncomputable def source {q : ℕ} (j : Fin q) : Stack q :=
  .inl (.inl (.inl (.inl (j, 1))))

noncomputable def target {q : ℕ} : Stack q :=
  SourceClauseRowWriterOperands.gateCell
    (SourceClauseRowWriterOperands.gateLiteral (.inl 0))

noncomputable def temp {q : ℕ} : Stack q :=
  SourceClauseRowWriterOperands.scratch

noncomputable def program {q : ℕ} (j : Fin q) :=
  SourceClausePreservingBroadcast.program (source j) temp [target]

noncomputable def after {q : ℕ} (j : Fin q)
    (bits : List Bool) (S : Stack q → List Bool) :=
  SourceClausePreservingBroadcast.result (source j) temp [target] bits S

theorem source_ne_temp {q : ℕ} (j : Fin q) :
    source j ≠ (temp : Stack q) := by
  simp [source, temp, SourceClauseRowWriterOperands.scratch]

theorem target_local_not_core {q : ℕ} :
    (SourceClauseRowWriterOperands.gateLiteral (.inl 0) :
      SourceClauseRowWriterCore.Gate q) ∉
      Set.range (SourceClauseRowWriterCore.gateCore (q := q)) := by
  rintro ⟨c, hc⟩
  cases c with
  | inl x =>
      simp [SourceClauseRowWriterOperands.gateLiteral,
        SourceClauseRowWriterCore.gateCore,
        SourceClauseRowWriterCore.gateCoreCell,
        SourceClauseRowGateCleanup.rowCell,
        SourceClauseRowIndexedGate.gateEmbedding,
        SourceClauseRowGate.addressEmbedding] at hc
  | inr z =>
      fin_cases z <;>
        simp [SourceClauseRowWriterOperands.gateLiteral,
          SourceClauseRowWriterCore.gateCore,
          SourceClauseRowWriterCore.gateCoreCell,
          SourceClauseRowGateCleanup.savedCell,
          SourceClauseRowGateCleanup.outputCell,
          SourceClauseRowGateCleanup.countCell,
          SourceClauseRowIndexedGate.gateEmbedding,
          SourceClauseRowGate.gateEmbedding,
          SourceClauseRowGate.addressEmbedding,
          SourceClauseGateSlotAddress.gateEmbedding] at hc

theorem source_ne_target {q : ℕ} (j : Fin q) :
    source j ≠ (target : Stack q) := by
  have hcore : (SourceClauseRowWriterOperands.gateLiteral (.inl 0) :
      SourceClauseRowWriterCore.Gate q) ∉
      Set.range (SourceClauseRowWriterCore.gateCore (q := q)) := by
    rintro ⟨c, hc⟩
    cases c with
    | inl x =>
        simp [SourceClauseRowWriterOperands.gateLiteral,
          SourceClauseRowWriterCore.gateCore,
          SourceClauseRowWriterCore.gateCoreCell,
          SourceClauseRowGateCleanup.rowCell,
          SourceClauseRowIndexedGate.gateEmbedding,
          SourceClauseRowGate.addressEmbedding] at hc
    | inr z =>
        fin_cases z <;>
          simp [SourceClauseRowWriterOperands.gateLiteral,
            SourceClauseRowWriterCore.gateCore,
            SourceClauseRowWriterCore.gateCoreCell,
            SourceClauseRowGateCleanup.savedCell,
            SourceClauseRowGateCleanup.outputCell,
            SourceClauseRowGateCleanup.countCell,
            SourceClauseRowIndexedGate.gateEmbedding,
            SourceClauseRowGate.gateEmbedding,
            SourceClauseRowGate.addressEmbedding,
            SourceClauseGateSlotAddress.gateEmbedding] at hc
  have h := SourceClauseRowWriterStageReady.gate_scratch_ne_core
    (SourceClauseRowWriterOperands.gateLiteral (.inl 0)) hcore
    (.inl (.inl (j, 1)) : SourceClauseRowWriterCore.Core q)
  simpa [source, target, SourceClauseRowWriterOperands.gateCell]
    using h.symm

theorem temp_ne_target {q : ℕ} :
    (temp : Stack q) ≠ target := by
  simp [temp, target, SourceClauseRowWriterOperands.scratch,
    SourceClauseRowWriterOperands.gateCell]

theorem run {q : ℕ} (j : Fin q)
    (bits : List Bool) (S : Stack q → List Bool)
    (hs : S (source j) = bits) (ht : S temp = []) :
    ((advance (program j))^[2 * bits.length + 3])
      (⟨some SourceClausePreservingBroadcast.Label.scan, ((), none), S⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          SourceClausePreservingBroadcast.Label (Unit × Option Bool)) =
      ⟨none, ((), none), after j bits S⟩ := by
  exact SourceClausePreservingBroadcast.run_halt
    (source j) temp [target] (source_ne_temp j) (by simp)
    (by simp [source_ne_target j]) (by simp [temp_ne_target])
    bits S hs ht

theorem source_restored {q : ℕ} (j : Fin q)
    (bits : List Bool) (S : Stack q → List Bool) :
    after j bits S (source j) = bits :=
  SourceClausePreservingBroadcast.source_restored
    (source j) temp [target] (source_ne_temp j) bits S

end EthInapproximability.CurrentPaper.SourceClauseRowWriterQueryEcho
