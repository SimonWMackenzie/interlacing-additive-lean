import EthInapproximability.CurrentPaper.GenericPrefixGateOperands
import EthInapproximability.CurrentPaper.SourceGenericPrefix
import EthInapproximability.CurrentPaper.SourceClausePrefixGateCycle

/-! Generic-alphabet exact address/byte interface of the checked physical
row-derived gate. Operand staging into its initial bank is separate. -/

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.GateSemantic

open Turing BitMachineEncoding
open SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open SourceGenericPrefix SourceBooleanPrefix

theorem bitIndex_val {n a : Nat} (v : Fin n) (s : Fin a) :
    (bitIndex v s).val = v.val * a + s.val := by
  simp [bitIndex, finProdFinEquiv]
  ring

theorem gate_address (n a q ordinal position : Nat) :
    ordinal * (width a q + 1) + (n * a + position) =
      SourceGenericPrefix.base n a q ordinal + position := by
  simp [SourceGenericPrefix.base]
  omega

theorem run {n a q : Nat} (v : Fin n) (s : Fin a)
    (ordinal position : Nat) (sign : Bool)
    (saved output count : List Bool) :
    ∃ T ≤ SourceClauseRowGate.cost v.val a s.val n position ordinal
        (width a q + 1) sign,
      ((advance (SourceClauseRowGate.program (0 : Fin 1) sign))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))),
          SourceBooleanPrefix.PrefixGateCycle.gateControl,
          SourceClauseRowGate.initial (vertexFrame v)
            v.val a s.val n position ordinal (width a q + 1)
            saved output count⟩) =
        ⟨none,SourceBooleanPrefix.PrefixGateCycle.gateControl,
          SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
            v.val a s.val n position ordinal (width a q + 1)
            sign saved output count⟩ := by
  exact SourceClauseRowGate.run (0 : Fin 1) (vertexFrame v)
    v.val a s.val n position ordinal (width a q + 1) sign
    saved output count (vertexFrame_query v)

theorem final_saved {n a q : Nat} (v : Fin n) (s : Fin a)
    (ordinal position : Nat) (sign : Bool)
    (saved output count : List Bool) :
    SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val a s.val n position ordinal (width a q + 1)
      sign saved output count SourceBooleanPrefix.gateSavedKey =
      (clauseFields (orGate
        (SourceGenericPrefix.base n a q ordinal + position)
        ⟨bitIndex v s,sign⟩)).reverse ++ saved := by
  rw [SourceBooleanPrefix.gateSavedKey,SourceClauseRowGate.final_saved]
  rw [← gate_address n a q ordinal position]
  simp [bitIndex_val,orGate,
    SourceClauseGatePrepare.firstClause,
    SourceClauseGatePrepare.secondClause,
    SourceClauseGatePrepare.thirdClause,
    clauseFields,List.reverse_append,List.append_assoc]

theorem final_count {n a q : Nat} (v : Fin n) (s : Fin a)
    (ordinal position : Nat) (sign : Bool)
    (saved output count : List Bool) :
    SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val a s.val n position ordinal (width a q + 1)
      sign saved output count SourceBooleanPrefix.gateCountKey =
      true :: true :: true :: count := by
  exact SourceClauseRowGate.final_count (0 : Fin 1) (vertexFrame v)
    v.val a s.val n position ordinal (width a q + 1) sign
    saved output count

#print axioms run
#print axioms final_saved

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.GateSemantic
