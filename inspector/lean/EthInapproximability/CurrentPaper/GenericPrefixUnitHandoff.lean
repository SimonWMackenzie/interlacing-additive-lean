import EthInapproximability.CurrentPaper.GenericPrefixUnitClean
import EthInapproximability.CurrentPaper.SourceClausePrefixResumePieces

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.UnitHandoff

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanPrefix SourceClauseEncoding
open scoped Classical

def nextSaved (n a ordinal w ell : Nat) (sign : Bool)
    (saved : List Bool) : List Bool :=
  (EncodedCNF.encodeClause (SourceClauseUnitMachine.unitClause
    (ordinal*w+(n*a+ell)) sign)).reverse ++ saved

theorem after_clear (n a ordinal w ell : Nat) (sign : Bool)
    (saved output count : List Bool)
    (foreign : PrefixSharedCore.Stack → List Bool) :
    SourceClauseClearExcept.result PrefixSharedClear.keep
      (bank PrefixSharedCore.unitEmbedding foreign
        (UnitRun.finished n a ordinal w ell sign saved output count)) =
      PrefixGateReady.blank n ordinal
        (nextSaved n a ordinal w ell sign saved)
        output (true :: count) := by
  apply PrefixSharedClear.result_eq_blank
  intro i
  rw [← SourceClauseSharedCore.right_core PrefixSharedCore.gateCore
      PrefixSharedCore.unitCore i]
  change bank PrefixSharedCore.unitEmbedding foreign
    (UnitRun.finished n a ordinal w ell sign saved output count)
    (PrefixSharedCore.unitEmbedding (PrefixSharedCore.unitCore i)) = _
  rw [bank_at]
  have hi : PrefixSharedCore.unitCore i ∈ PrefixUnitClean.keep := by
    exact (PrefixSharedUnitReady.keep_iff _).mpr ⟨i,rfl⟩
  have hfin := congrFun
    (UnitClean.clean_finished_eq_blank n a ordinal w ell sign
      saved output count) (PrefixSharedCore.unitCore i)
  rw [PrefixUnitClean.clean,SourceClauseClearExcept.result,
    if_pos hi] at hfin
  rw [hfin]
  fin_cases i
  · exact PrefixUnitClean.blank_vertexCount n ordinal _ _ _
  · exact PrefixUnitClean.blank_ordinal n ordinal _ _ _
  · exact PrefixUnitClean.blank_saved n ordinal _ _ _
  · exact PrefixUnitClean.blank_output n ordinal _ _ _
  · exact PrefixUnitClean.blank_count n ordinal _ _ _

#print axioms after_clear

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.UnitHandoff
