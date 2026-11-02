import EthInapproximability.CurrentPaper.GenericPrefixGateReady
import EthInapproximability.CurrentPaper.SourceClausePairGatePatch

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairGateBase

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanPrefix
open scoped Classical

abbrev Stack := PairUnitLift.Stack

noncomputable def preparationProgram (a : Nat) (bit : Fin a) (w : Nat) :=
  fun l => stackStmt SourceBooleanPrefix.PairGateBase.coreEmbedding
    (GateOperands.program a bit.val w l)

theorem preparation_run {n a : Nat} (v : Fin n) (bit : Fin a)
    (ordinal w : Nat) (saved output count : List Bool) :
    ∃ t ≤ GateOperands.cost a bit.val w
      (List.replicate v.val true),
      ((advance (preparationProgram a bit w))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (SourceClauseFixedBatch.labelAt
            (GateOperands.constantSize a bit.val w) 0)),
          ((),((),none)),
          PairUnitLift.pairBank n v.val ordinal saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,((),((),none)),
          bank SourceBooleanPrefix.PairGateBase.coreEmbedding
            (SourceBooleanPrefix.PairGateBase.ordinalForeign ordinal)
            (GateReady.prepared v bit w saved output count)⟩ := by
  obtain ⟨t,ht,hrun⟩ := GateReady.prepared_run v bit w
    saved output count
  have h := BitMachineStackRun.run
    SourceBooleanPrefix.PairGateBase.coreEmbedding
    (SourceBooleanPrefix.PairGateBase.ordinalForeign ordinal)
    (GateOperands.program a bit.val w)
    (⟨some (BitMachineRawSequence.leftLabel
      (SourceClauseFixedBatch.labelAt
        (GateOperands.constantSize a bit.val w) 0)),
      ((),((),none)),
      PrefixGateReady.blank n v.val saved output count⟩ :
      TM2.Cfg (fun _ : PrefixSharedCore.Stack => Bool) _ _) t
  rw [hrun] at h
  refine ⟨t,ht,?_⟩
  have hb : bank SourceBooleanPrefix.PairGateBase.coreEmbedding
      (SourceBooleanPrefix.PairGateBase.ordinalForeign ordinal)
      (PrefixGateReady.blank n v.val saved output count) =
      PairUnitLift.pairBank n v.val ordinal saved output count :=
    SourceBooleanPrefix.PairGateBase.gateBlank_eq_pairBank
      n v.val ordinal saved output count
  simp only [stackCfg,hb] at h
  simpa only [preparationProgram] using h

#print axioms preparation_run

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairGateBase
