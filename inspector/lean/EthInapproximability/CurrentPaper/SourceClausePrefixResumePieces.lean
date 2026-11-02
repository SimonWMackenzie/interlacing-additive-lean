import EthInapproximability.CurrentPaper.SourceClausePrefixGateReady
import EthInapproximability.CurrentPaper.SourceClausePrefixSharedUnitReady
import EthInapproximability.CurrentPaper.SourceClausePrefixSharedClear
import EthInapproximability.CurrentPaper.SourceClausePrefixSharedGateN
import EthInapproximability.CurrentPaper.SourceClauseFixedBatch

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

namespace PrefixSharedUnitStage

noncomputable def program (w ell : ℕ) :=
  PrefixSharedExecution.liftedProgram PrefixSharedCore.unitEmbedding
    (SourceClauseFixedBatch.program PrefixUnitClean.constantTarget
      (PrefixUnitClean.constantSize w ell))

theorem run (n ordinal w ell : ℕ)
    (saved output count : List Bool)
    (foreign : PrefixSharedCore.Stack → List Bool) :
    ∃ t ≤ SourceClauseFixedBatch.costPrefix
        (PrefixUnitClean.constantSize w ell) 3 + 1,
      ((advance (program w ell))^[t])
        (stackCfg PrefixSharedCore.unitEmbedding foreign
          ⟨some (SourceClauseFixedBatch.labelAt
            (PrefixUnitClean.constantSize w ell) 0), (),
            PrefixUnitClean.blank n ordinal saved output count⟩) =
        stackCfg PrefixSharedCore.unitEmbedding foreign
          ⟨none, (),
            PrefixUnitRun.initial n ordinal w ell saved output count⟩ := by
  have h := PrefixUnitClean.stage_run w ell
    (PrefixUnitClean.blank n ordinal saved output count)
  rw [PrefixUnitClean.stage_blank_eq_initial] at h
  obtain ⟨t, ht, hr⟩ := PrefixSharedExecution.lifted_run
    PrefixSharedCore.unitEmbedding foreign
    (SourceClauseFixedBatch.program PrefixUnitClean.constantTarget
      (PrefixUnitClean.constantSize w ell)) _ _
    (SourceClauseFixedBatch.costPrefix
      (PrefixUnitClean.constantSize w ell) 3 + 1) h rfl
  exact ⟨t, ht, hr⟩

theorem initial_master_bank (n ordinal : ℕ)
    (saved output count : List Bool) :
    bank PrefixSharedCore.unitEmbedding
      (PrefixGateReady.blank n ordinal saved output count)
      (PrefixUnitClean.blank n ordinal saved output count) =
    PrefixGateReady.blank n ordinal saved output count := by
  apply bank_eq_self
  intro x
  exact (PrefixSharedUnitReady.blank_ready n ordinal
    saved output count x).symm

end PrefixSharedUnitStage

namespace PrefixSharedUnitHandoff

open SourceClauseEncoding

def nextSaved (n ordinal w ell : ℕ) (sign : Bool)
    (saved : List Bool) : List Bool :=
  (EncodedCNF.encodeClause (SourceClauseUnitMachine.unitClause
    (ordinal * w + (2 * n + ell)) sign)).reverse ++ saved

theorem after_clear (n ordinal w ell : ℕ) (sign : Bool)
    (saved output count : List Bool)
    (foreign : PrefixSharedCore.Stack → List Bool) :
    SourceClauseClearExcept.result PrefixSharedClear.keep
      (bank PrefixSharedCore.unitEmbedding foreign
        (PrefixUnitRun.finished n ordinal w ell sign saved output count)) =
      PrefixGateReady.blank n ordinal
        (nextSaved n ordinal w ell sign saved) output (true :: count) := by
  apply PrefixSharedClear.result_eq_blank
  intro i
  rw [← SourceClauseSharedCore.right_core PrefixSharedCore.gateCore
      PrefixSharedCore.unitCore i]
  change bank PrefixSharedCore.unitEmbedding foreign
    (PrefixUnitRun.finished n ordinal w ell sign saved output count)
    (PrefixSharedCore.unitEmbedding (PrefixSharedCore.unitCore i)) = _
  rw [bank_at]
  have hi : PrefixSharedCore.unitCore i ∈ PrefixUnitClean.keep := by
    exact (PrefixSharedUnitReady.keep_iff _).mpr ⟨i, rfl⟩
  have hfin := congrFun
    (PrefixUnitClean.clean_finished_eq_blank n ordinal w ell sign
      saved output count) (PrefixSharedCore.unitCore i)
  rw [PrefixUnitClean.clean, SourceClauseClearExcept.result,
    if_pos hi] at hfin
  rw [hfin]
  fin_cases i
  · exact PrefixUnitClean.blank_vertexCount n ordinal _ _ _
  · exact PrefixUnitClean.blank_ordinal n ordinal _ _ _
  · exact PrefixUnitClean.blank_saved n ordinal _ _ _
  · exact PrefixUnitClean.blank_output n ordinal _ _ _
  · exact PrefixUnitClean.blank_count n ordinal _ _ _

end PrefixSharedUnitHandoff

namespace PrefixSharedGateHandoff

open SourceBooleanEncoding SourceClauseEncoding EncodedCNF

def nextSaved {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved : List Bool) : List Bool :=
  (clauseFields (orGate (base n q (atLeastOrdinal v) + s.val)
    (SourceBooleanEncoding.positive (bitIndex v s)))).reverse ++ saved

theorem after_clear {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool)
    (foreign : PrefixSharedCore.Stack → List Bool) :
    SourceClauseClearExcept.result PrefixSharedClear.keep
      (bank PrefixSharedCore.gateEmbedding foreign
        (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
          v.val 2 s.val n s.val v.val (width 2 q + 1) true
          saved output count)) =
      PrefixGateReady.blank n v.val (nextSaved (q := q) v s saved)
        output (true :: true :: true :: count) := by
  apply PrefixSharedClear.result_eq_blank
  intro i
  rw [← SourceClauseSharedCore.left_core PrefixSharedCore.gateCore
      PrefixSharedCore.unitCore i]
  change bank PrefixSharedCore.gateEmbedding foreign
    (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val 2 s.val n s.val v.val (width 2 q + 1) true
      saved output count)
    (PrefixSharedCore.gateEmbedding (PrefixSharedCore.gateCore i)) = _
  rw [bank_at]
  fin_cases i
  · exact PrefixSharedGateN.gateN_final v s saved output count
  · have h := PrefixGateClean.final_row (q := q) v s saved output count
      (.inl ((0 : Fin 1), 1))
    rw [PrefixGateClean.clean, SourceClauseClearExcept.result,
      if_pos (PrefixGateClean.row_mem _)] at h
    simpa [PrefixGateClean.rowCell, PrefixSharedCore.gateCore,
      PrefixSharedCore.gateCoreCell, PrefixSharedCore.gateVertex,
      vertexFrame, PrefixGateReady.coreWords] using h
  · have h := PrefixGateClean.final_saved (q := q) v s saved output count
    rw [PrefixGateClean.clean, SourceClauseClearExcept.result,
      if_pos PrefixGateClean.saved_mem] at h
    exact h
  · have h := PrefixGateClean.final_output (q := q) v s
      saved output count
    rw [PrefixGateClean.clean, SourceClauseClearExcept.result,
      if_pos PrefixGateClean.output_mem] at h
    exact h
  · have h := PrefixGateClean.final_count (q := q) v s
      saved output count
    rw [PrefixGateClean.clean, SourceClauseClearExcept.result,
      if_pos PrefixGateClean.count_mem] at h
    exact h

end PrefixSharedGateHandoff

namespace PrefixSharedUnitPair

noncomputable def program (w ell : ℕ) (sign : Bool) :=
  BitMachineRawSequence.program
    (PrefixSharedUnitStage.program w ell)
    (PrefixSharedUnit.program sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            MatrixAddressMachine.Label.outer))))
    () PrefixUnitRun.startControl

theorem run (n ordinal w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    ∃ t ≤ (SourceClauseFixedBatch.costPrefix
          (PrefixUnitClean.constantSize w ell) 3 + 1) +
        PrefixUnitRun.cost n ordinal w ell + 1,
      ((advance (program w ell sign))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (SourceClauseFixedBatch.labelAt
              (PrefixUnitClean.constantSize w ell) 0)),
          ((), PrefixUnitRun.startControl),
          PrefixGateReady.blank n ordinal saved output count⟩) =
        ⟨none, ((), PrefixUnitRun.startControl),
          bank PrefixSharedCore.unitEmbedding
            (PrefixGateReady.blank n ordinal saved output count)
            (PrefixUnitRun.finished n ordinal w ell sign
              saved output count)⟩ := by
  let B := PrefixGateReady.blank n ordinal saved output count
  obtain ⟨a, ha, hA⟩ := PrefixSharedUnitStage.run n ordinal w ell
    saved output count B
  obtain ⟨b, hb, hB⟩ := PrefixSharedUnit.run n ordinal w ell sign
    saved output count B
  have hA' :
      ((advance (PrefixSharedUnitStage.program w ell))^[a])
        (⟨some (SourceClauseFixedBatch.labelAt
          (PrefixUnitClean.constantSize w ell) 0), (), B⟩) =
        ⟨none, (), bank PrefixSharedCore.unitEmbedding B
          (PrefixUnitRun.initial n ordinal w ell saved output count)⟩ := by
    dsimp only [stackCfg] at hA
    rw [show bank PrefixSharedCore.unitEmbedding B
      (PrefixUnitClean.blank n ordinal saved output count) = B from
      PrefixSharedUnitStage.initial_master_bank n ordinal saved output count]
      at hA
    exact hA
  have hB' :
      ((advance (PrefixSharedUnit.program sign))^[b])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                MatrixAddressMachine.Label.outer)))),
          PrefixUnitRun.startControl,
          bank PrefixSharedCore.unitEmbedding B
            (PrefixUnitRun.initial n ordinal w ell saved output count)⟩) =
        ⟨none, PrefixUnitRun.startControl,
          bank PrefixSharedCore.unitEmbedding B
            (PrefixUnitRun.finished n ordinal w ell sign saved output count)⟩ := by
    simpa only [stackCfg] using hB
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs
    (PrefixSharedUnitStage.program w ell) (PrefixSharedUnit.program sign)
    (SourceClauseFixedBatch.labelAt
      (PrefixUnitClean.constantSize w ell) 0)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            MatrixAddressMachine.Label.outer))))
    () () PrefixUnitRun.startControl PrefixUnitRun.startControl
    B (bank PrefixSharedCore.unitEmbedding B
      (PrefixUnitRun.initial n ordinal w ell saved output count))
    (bank PrefixSharedCore.unitEmbedding B
      (PrefixUnitRun.finished n ordinal w ell sign saved output count))
    a b hA' hB'
  exact ⟨t, by omega, h⟩

end PrefixSharedUnitPair
end EthInapproximability.CurrentPaper.SourceBooleanPrefix

#print axioms EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixSharedUnitPair.run
