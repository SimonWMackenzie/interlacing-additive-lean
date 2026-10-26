import EthInapproximability.CurrentPaper.GenericPrefixGateReady
import EthInapproximability.CurrentPaper.GenericPrefixGateSemantic

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.GateHandoff

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open SourceBooleanPrefix SourceGenericPrefix

def nextSaved {n a q : Nat} (v : Fin n) (s : Fin a)
    (saved : List Bool) : List Bool :=
  (clauseFields (orGate
    (SourceGenericPrefix.base n a q (SourceGenericPrefix.atLeastOrdinal v) + s.val)
    ⟨bitIndex v s,true⟩)).reverse ++ saved

theorem generic_n {n a q : Nat} (v : Fin n) (s : Fin a)
    (saved output count : List Bool) :
    SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val a s.val n s.val v.val (width a q + 1) true
      saved output count PrefixSharedCore.gateN =
        List.replicate n true := by
  rw [SourceClauseRowGate.finalBank, show PrefixSharedCore.gateN =
    SourceClauseRowGate.gateEmbedding (.inl 0) by rfl, bank_at]
  rw [SourceClauseGateSlotAddress.finalBank, bank_outside]
  · simp [SourceClauseGateSlotAddress.transferred,
      BitMachineBroadcast.copied,SourceClauseGateSlotAddress.offsetDone,
      SourceClauseGateSlotAddress.offsetOutput,
      SourceClauseGateSlotAddress.offsetSource,
      SourceClauseGateSlotAddress.temp,
      SourceClauseGateSlotAddress.targets,
      SourceClauseGateSlotAddress.affineOffset,
      MatrixAddressMachine.cfg]
  · intro ⟨x,h⟩; cases h

theorem generic_output {n a q : Nat} (v : Fin n) (s : Fin a)
    (saved output count : List Bool) :
    SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val a s.val n s.val v.val (width a q + 1) true
      saved output count PrefixGateClean.outputCell = output := by
  simp only [PrefixGateClean.outputCell,SourceClauseRowGate.finalBank,
    bank_at,SourceClauseGateSlotAddress.final_output]

theorem after_clear {n a q : Nat} (v : Fin n) (s : Fin a)
    (saved output count : List Bool)
    (foreign : PrefixSharedCore.Stack → List Bool) :
    SourceClauseClearExcept.result PrefixSharedClear.keep
      (bank PrefixSharedCore.gateEmbedding foreign
        (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
          v.val a s.val n s.val v.val (width a q + 1) true
          saved output count)) =
      PrefixGateReady.blank n v.val
        (nextSaved (q := q) v s saved)
        output (true :: true :: true :: count) := by
  apply PrefixSharedClear.result_eq_blank
  intro i
  rw [← SourceClauseSharedCore.left_core PrefixSharedCore.gateCore
      PrefixSharedCore.unitCore i]
  change bank PrefixSharedCore.gateEmbedding foreign
    (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val a s.val n s.val v.val (width a q + 1) true
      saved output count)
    (PrefixSharedCore.gateEmbedding (PrefixSharedCore.gateCore i)) = _
  rw [bank_at]
  fin_cases i
  · exact generic_n v s saved output count
  · have h := SourceClauseRowGate.final_row (0 : Fin 1) (vertexFrame v)
      v.val a s.val n s.val v.val (width a q + 1) true
      saved output count (vertexFrame_query v) (.inl ((0 : Fin 1), 1))
    simpa [PrefixSharedCore.gateCore,PrefixSharedCore.gateCoreCell,
      PrefixSharedCore.gateVertex,vertexFrame,PrefixGateReady.coreWords]
      using h
  · simpa [PrefixSharedCore.gateCore,PrefixSharedCore.gateCoreCell,
      PrefixGateClean.savedCell,PrefixGateReady.coreWords,nextSaved]
      using GateSemantic.final_saved (q := q) v s v.val s.val true
        saved output count
  · exact generic_output v s saved output count
  · simpa [PrefixSharedCore.gateCore,PrefixSharedCore.gateCoreCell,
      PrefixGateClean.countCell,PrefixGateReady.coreWords]
      using GateSemantic.final_count (q := q) v s v.val s.val true
        saved output count

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.GateHandoff
