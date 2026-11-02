import EthInapproximability.CurrentPaper.SourceClausePrefixUnitReset
import EthInapproximability.CurrentPaper.SourceClausePrefixGateCleanRun
import EthInapproximability.CurrentPaper.SourceClauseSharedCore

/-!
A physical master bank for prefix units and at-least OR gates. Its five
shared cells are unary n, unary vertex/clause ordinal, reverse CNF payload,
output suffix, and unary emitted-clause count. All other local scratch stays
disjoint. This is a bank-layout theorem, not a charged preparation program.
-/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixSharedCore

open scoped Classical

abbrev Core := Fin 5
abbrev Gate := SourceClauseRowGate.Stack 1
abbrev UnitBank := PrefixUnitRun.Stack

def gateN : Gate := .inr (.inl (.inl 0))
def gateVertex : Gate := .inl (.inl (.inl ((0 : Fin 1), 1)))

def gateCoreCell : Core → Gate
  | 0 => gateN
  | 1 => gateVertex
  | 2 => PrefixGateClean.savedCell
  | 3 => PrefixGateClean.outputCell
  | 4 => PrefixGateClean.countCell

def unitCoreCell : Core → UnitBank
  | 0 => PrefixUnitClean.vertexCount
  | 1 => PrefixUnitClean.ordinal
  | 2 => PrefixUnitClean.saved
  | 3 => PrefixUnitClean.output
  | 4 => PrefixUnitClean.count

def gateCore : Core ↪ Gate where
  toFun := gateCoreCell
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp [gateCoreCell, gateN, gateVertex, PrefixGateClean.savedCell,
        PrefixGateClean.outputCell, PrefixGateClean.countCell,
        SourceClauseRowGate.gateEmbedding,
        SourceClauseGateSlotAddress.gateEmbedding,
        SourceClauseGateAffineAddress.gateEmbedding,
        SourceClauseGateTwoAddress.embedding,
        SourceClauseGateMachine.embedding, gateSavedKey, gateCountKey] at h ⊢

def unitCore : Core ↪ UnitBank where
  toFun := unitCoreCell
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp [unitCoreCell, PrefixUnitClean.vertexCount,
        PrefixUnitClean.ordinal, PrefixUnitClean.saved,
        PrefixUnitClean.output, PrefixUnitClean.count,
        PrefixUnitRun.savedKey, PrefixUnitRun.outputKey,
        PrefixUnitRun.countKey,
        SourceClauseGateSlotAddress.gateEmbedding,
        SourceClauseGateAffineAddress.addressEmbedding] at h ⊢

noncomputable abbrev Stack :=
  SourceClauseSharedCore.Stack gateCore unitCore

noncomputable def gateEmbedding : Gate ↪ Stack :=
  SourceClauseSharedCore.left gateCore unitCore

noncomputable def unitEmbedding : UnitBank ↪ Stack :=
  SourceClauseSharedCore.right gateCore unitCore

theorem same_cell (i : Core) :
    gateEmbedding (gateCore i) = unitEmbedding (unitCore i) :=
  SourceClauseSharedCore.shared gateCore unitCore i

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixSharedCore
