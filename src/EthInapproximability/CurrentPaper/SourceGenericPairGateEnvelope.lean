import EthInapproximability.CurrentPaper.SourceGenericPairUnitEnvelope
import EthInapproximability.CurrentPaper.SourceClausePairGateCost

/-! Growth envelope for the physical generic gate cleanup. -/

namespace EthInapproximability.CurrentPaper.SourceGenericPairEnumeration

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceGenericPrefixMachine SourceBooleanPrefix
set_option maxHeartbeats 2000000

noncomputable def gatePre {n a : Nat} (v : Fin n) (bit : Fin a)
    (ell : Fin 2) (ordinal w : Nat) (sign : Bool) : Nat :=
  GateOperands.cost a bit.val w (List.replicate v.val true) +
    (v.val+bit.val+4)+(2*ordinal+2)+
    (PairGatePatch.offsetSize ell 0+2)+3+
    SourceClauseRowGate.cost v.val a bit.val n ell.val ordinal w sign+1

theorem gate_first_run {n a : Nat} (v : Fin n) (bit : Fin a)
    (ell : Fin 2) (ordinal w : Nat) (sign : Bool)
    (saved output count : List Bool) :
    ∃ u ≤ gatePre v bit ell ordinal w sign,
      ((advance (PairGateCycle.firstProgram bit ell sign w))^[u])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (SourceClauseFixedBatch.labelAt
                    (GateOperands.constantSize a bit.val w) 0)))))),
          ((((((), ((), none)), ((), none)), none), ()),
            SourceGenericPrefixMachine.PairGateExecute.gateControl),
          PairUnitLift.pairBank n v.val ordinal saved output count⟩) =
        ⟨none,
          ((((((), ((), none)), ((), none)), none), ()),
            SourceGenericPrefixMachine.PairGateExecute.gateControl),
          SourceGenericPrefixMachine.PairGateExecute.finished v bit ell.val ordinal w sign
            saved output count⟩ := by
  let B0 := PairUnitLift.pairBank n v.val ordinal saved output count
  let B1 := SourceGenericPrefixMachine.PairGatePrep.ready v bit w ordinal ell.val saved output count
  let B2 := SourceGenericPrefixMachine.PairGateExecute.finished v bit ell.val ordinal w sign
    saved output count
  obtain ⟨p,hp,hP⟩ := SourceGenericPrefixMachine.PairGatePrep.run v bit ell w ordinal saved output count
  obtain ⟨g,hg,hG⟩ := SourceGenericPrefixMachine.PairGateExecute.run v bit ell.val ordinal w sign
    saved output count
  obtain ⟨u,hu,hU⟩ := BitMachineRawSequence.runs
    (SourceGenericPrefixMachine.PairGatePrep.program a bit ell w) (SourceGenericPrefixMachine.PairGateExecute.program sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (SourceClauseFixedBatch.labelAt
              (GateOperands.constantSize a bit.val w) 0)))))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)))
    (((((), ((), none)), ((), none)), none), ())
    (((((), ((), none)), ((), none)), none), ())
    SourceGenericPrefixMachine.PairGateExecute.gateControl SourceGenericPrefixMachine.PairGateExecute.gateControl
    B0 B1 B2 p g hP hG
  refine ⟨u, ?_, ?_⟩
  · dsimp only [gatePre]
    omega
  · simpa only [SourceGenericPrefixMachine.PairGateCycle.firstProgram, B0, B2] using hU

theorem gate_cost_le_envelope {n a : Nat} (v : Fin n) (bit : Fin a)
    (ell : Fin 2) (ordinal w : Nat) (sign : Bool)
    (saved output count : List Bool) :
    PairOneMachine.gateCost v bit ell ordinal w sign saved output count ≤
      gatePre v bit ell ordinal w sign +
      PairGateCost.workCount *
        ((n+v.val+ordinal+saved.length+output.length+count.length) +
          BitMachineStackGrowth.perStep
            (SourceGenericPrefixMachine.PairGateCycle.firstProgram bit ell sign w) *
              gatePre v bit ell ordinal w sign) +
      PairGateCost.workCount+3 := by
  obtain ⟨u,hu,hr⟩ := gate_first_run v bit ell ordinal w sign
    saved output count
  have hc := PairGateCost.clear_after_run
    (SourceGenericPrefixMachine.PairGateCycle.firstProgram bit ell sign w)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (SourceClauseFixedBatch.labelAt
                (GateOperands.constantSize a bit.val w) 0))))))
    ((((((), ((), none)), ((), none)), none), ()),
      SourceGenericPrefixMachine.PairGateExecute.gateControl)
    (PairUnitLift.pairBank n v.val ordinal saved output count)
    (SourceGenericPrefixMachine.PairGateExecute.finished v bit ell.val ordinal w sign
      saved output count)
    u (gatePre v bit ell ordinal w sign)
    (n+v.val+ordinal+saved.length+output.length+count.length)
    hu hr (PairGateCost.pair_blank_word_bound n v.val ordinal
      saved output count)
  change gatePre v bit ell ordinal w sign +
    PrefixSharedClear.cost
      (SourceGenericPrefixMachine.PairGateCleanup.localBank
        v bit ell.val ordinal w sign saved output count) + 1 ≤ _
  have hbank : PrefixSharedClear.cost
      (SourceGenericPrefixMachine.PairGateCleanup.localBank
        v bit ell.val ordinal w sign saved output count) =
      PrefixSharedClear.cost (fun x =>
        SourceGenericPrefixMachine.PairGateExecute.finished
          v bit ell.val ordinal w sign saved output count
            (PairGateBase.coreEmbedding x)) := rfl
  rw [hbank]
  omega

#print axioms gate_first_run
#print axioms gate_cost_le_envelope

end EthInapproximability.CurrentPaper.SourceGenericPairEnumeration
