import EthInapproximability.CurrentPaper.SourceGenericPairGatePolynomial
import EthInapproximability.CurrentPaper.SourceClausePrefixLoopCost

/-! Cleanup charge for the real generic unit phase, obtained from growth of
the actual fixed controller and the preceding physical run. -/

namespace EthInapproximability.CurrentPaper.SourceGenericPairEnumeration

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceGenericPrefixMachine SourceBooleanPrefix
set_option maxHeartbeats 2000000

theorem unit_cost_le_envelope (n a ordinal w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    UnitCycle.cost n a ordinal w ell sign saved output count ≤
      UnitCycle.pairCost n a ordinal w ell saved output count +
      PrefixLoopCost.workCount *
        ((n+ordinal+saved.length+output.length+count.length) +
          BitMachineStackGrowth.perStep
            (UnitCycle.pairProgram a w ell sign) *
              UnitCycle.pairCost n a ordinal w ell saved output count) +
      PrefixLoopCost.workCount+3 := by
  obtain ⟨t,ht,hr⟩ := UnitCycle.pair_run n a ordinal w ell sign
    saved output count
  have hc := PrefixLoopCost.clear_after_run
    (UnitCycle.pairProgram a w ell sign)
    (BitMachineRawSequence.leftLabel
      (SourceClauseFixedBatch.labelAt
        (UnitStage.constantSize a w ell) 0))
    ((), PrefixUnitRun.startControl)
    (PrefixGateReady.blank n ordinal saved output count)
    (bank PrefixSharedCore.unitEmbedding
      (PrefixGateReady.blank n ordinal saved output count)
      (UnitRun.finished n a ordinal w ell sign saved output count))
    t (UnitCycle.pairCost n a ordinal w ell saved output count)
    (n+ordinal+saved.length+output.length+count.length)
    ht hr (PrefixLoopCost.blank_word_bound n ordinal saved output count)
  dsimp only [UnitCycle.cost]
  omega

#print axioms unit_cost_le_envelope

end EthInapproximability.CurrentPaper.SourceGenericPairEnumeration
