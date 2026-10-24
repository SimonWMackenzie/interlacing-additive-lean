import EthInapproximability.CurrentPaper.GenericPrefixUnitCycle
import EthInapproximability.CurrentPaper.SourceClausePairUnitLift

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairUnit

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanPrefix
open scoped Classical

abbrev Stack := PairUnitLift.Stack

noncomputable def program (a w ell : Nat) (sign : Bool) :=
  fun l => stackStmt PairUnitLift.unitEmbedding
    (UnitCycle.program a w ell sign l)

theorem run (n a vertex ordinal w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    ∃ t ≤ UnitCycle.cost n a ordinal w ell sign saved output count,
      ((advance (program a w ell sign))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (SourceClauseFixedBatch.labelAt
              (UnitStage.constantSize a w ell) 0))),
          (((),PrefixUnitRun.startControl),((),none)),
          PairUnitLift.pairBank n vertex ordinal saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,(((),PrefixUnitRun.startControl),((),none)),
          PairUnitLift.pairBank n vertex ordinal
            (UnitHandoff.nextSaved n a ordinal w ell sign saved)
            output (true :: count)⟩ := by
  obtain ⟨t,ht,hrun⟩ := UnitCycle.run n a ordinal w ell sign
    saved output count
  have h := BitMachineStackRun.run PairUnitLift.unitEmbedding
    (fun x => if x = PairUnitLift.vertexCell then
      List.replicate vertex true else [])
    (UnitCycle.program a w ell sign)
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (SourceClauseFixedBatch.labelAt
          (UnitStage.constantSize a w ell) 0))),
      (((),PrefixUnitRun.startControl),((),none)),
      PrefixGateReady.blank n ordinal saved output count⟩ :
      TM2.Cfg (fun _ : PrefixSharedCore.Stack => Bool) _ _) t
  rw [hrun] at h
  exact ⟨t,ht,by simpa [program,PairUnitLift.pairBank] using h⟩

#print axioms run

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairUnit
