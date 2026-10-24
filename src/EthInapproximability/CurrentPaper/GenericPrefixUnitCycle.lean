import EthInapproximability.CurrentPaper.GenericPrefixUnitHandoff

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.UnitCycle

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanPrefix
open scoped Classical

noncomputable def stageProgram (a w ell : Nat) :=
  PrefixSharedExecution.liftedProgram PrefixSharedCore.unitEmbedding
    (SourceClauseFixedBatch.program PrefixUnitClean.constantTarget
      (UnitStage.constantSize a w ell))

noncomputable def pairProgram (a w ell : Nat) (sign : Bool) :=
  BitMachineRawSequence.program (stageProgram a w ell)
    (PrefixSharedUnit.program sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            MatrixAddressMachine.Label.outer))))
    () PrefixUnitRun.startControl

noncomputable def program (a w ell : Nat) (sign : Bool) :=
  BitMachineRawSequence.program (pairProgram a w ell sign)
    PrefixSharedClear.program (.clear 0)
    ((),PrefixUnitRun.startControl) ((),none)

noncomputable def pairCost (n a ordinal w ell : Nat)
    (saved output count : List Bool) :=
  SourceClauseFixedBatch.costPrefix (UnitStage.constantSize a w ell) 3 + 1 +
    UnitRun.cost n a ordinal w ell + 1

noncomputable def cost (n a ordinal w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :=
  pairCost n a ordinal w ell saved output count +
    PrefixSharedClear.cost
      (bank PrefixSharedCore.unitEmbedding
        (PrefixGateReady.blank n ordinal saved output count)
        (UnitRun.finished n a ordinal w ell sign saved output count)) + 1

theorem pair_run (n a ordinal w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    ∃ t ≤ pairCost n a ordinal w ell saved output count,
      ((advance (pairProgram a w ell sign))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (SourceClauseFixedBatch.labelAt
            (UnitStage.constantSize a w ell) 0)),
          ((),PrefixUnitRun.startControl),
          PrefixGateReady.blank n ordinal saved output count⟩) =
        ⟨none,((),PrefixUnitRun.startControl),
          bank PrefixSharedCore.unitEmbedding
            (PrefixGateReady.blank n ordinal saved output count)
            (UnitRun.finished n a ordinal w ell sign
              saved output count)⟩ := by
  let B := PrefixGateReady.blank n ordinal saved output count
  have hs := UnitStage.stage_run a w ell
    (PrefixUnitClean.blank n ordinal saved output count)
  rw [UnitStage.stage_blank_eq_initial] at hs
  obtain ⟨u,hu,hU⟩ := PrefixSharedExecution.lifted_run
    PrefixSharedCore.unitEmbedding B
    (SourceClauseFixedBatch.program PrefixUnitClean.constantTarget
      (UnitStage.constantSize a w ell)) _ _
    (SourceClauseFixedBatch.costPrefix
      (UnitStage.constantSize a w ell) 3 + 1) hs rfl
  have hA :
      ((advance (stageProgram a w ell))^[u])
        (⟨some (SourceClauseFixedBatch.labelAt
          (UnitStage.constantSize a w ell) 0),(),B⟩) =
        ⟨none,(),bank PrefixSharedCore.unitEmbedding B
          (UnitRun.initial n a ordinal w ell saved output count)⟩ := by
    dsimp only [stackCfg] at hU
    rw [show bank PrefixSharedCore.unitEmbedding B
      (PrefixUnitClean.blank n ordinal saved output count) = B from
      PrefixSharedUnitStage.initial_master_bank n ordinal
        saved output count] at hU
    exact hU
  obtain ⟨v,hv,hV⟩ := UnitRun.run n a ordinal w ell sign
    saved output count
  obtain ⟨b,hb,hB⟩ := PrefixSharedExecution.lifted_run
    PrefixSharedCore.unitEmbedding B
    (UnitRun.program sign) _ _ v hV rfl
  have hB' :
      ((advance (PrefixSharedUnit.program sign))^[b])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                MatrixAddressMachine.Label.outer)))),
          PrefixUnitRun.startControl,
          bank PrefixSharedCore.unitEmbedding B
            (UnitRun.initial n a ordinal w ell saved output count)⟩) =
        ⟨none,PrefixUnitRun.startControl,
          bank PrefixSharedCore.unitEmbedding B
            (UnitRun.finished n a ordinal w ell sign
              saved output count)⟩ := by
    simpa only [stackCfg,PrefixSharedUnit.program,UnitRun.program,
      UnitRun.startControl] using hB
  obtain ⟨t,ht,h⟩ := BitMachineRawSequence.runs
    (stageProgram a w ell) (PrefixSharedUnit.program sign)
    (SourceClauseFixedBatch.labelAt (UnitStage.constantSize a w ell) 0)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            MatrixAddressMachine.Label.outer))))
    () () PrefixUnitRun.startControl PrefixUnitRun.startControl
    B (bank PrefixSharedCore.unitEmbedding B
      (UnitRun.initial n a ordinal w ell saved output count))
    (bank PrefixSharedCore.unitEmbedding B
      (UnitRun.finished n a ordinal w ell sign saved output count))
    u b hA hB'
  exact ⟨t,by dsimp [pairCost]; omega,h⟩

theorem run (n a ordinal w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    ∃ t ≤ cost n a ordinal w ell sign saved output count,
      ((advance (program a w ell sign))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (SourceClauseFixedBatch.labelAt
              (UnitStage.constantSize a w ell) 0))),
          (((),PrefixUnitRun.startControl),((),none)),
          PrefixGateReady.blank n ordinal saved output count⟩) =
        ⟨none,(((),PrefixUnitRun.startControl),((),none)),
          PrefixGateReady.blank n ordinal
            (UnitHandoff.nextSaved n a ordinal w ell sign saved)
            output (true :: count)⟩ := by
  let B := PrefixGateReady.blank n ordinal saved output count
  let F := bank PrefixSharedCore.unitEmbedding B
    (UnitRun.finished n a ordinal w ell sign saved output count)
  obtain ⟨u,hu,hU⟩ := pair_run n a ordinal w ell sign
    saved output count
  have hC :
      ((advance PrefixSharedClear.program)^[PrefixSharedClear.cost F])
        (⟨some (.clear 0),((),none),F⟩) =
        ⟨none,((),none),PrefixGateReady.blank n ordinal
          (UnitHandoff.nextSaved n a ordinal w ell sign saved)
          output (true :: count)⟩ := by
    rw [PrefixSharedClear.run]
    exact congrArg (fun S => (⟨none,((),none),S⟩ :
      TM2.Cfg (fun _ : PrefixSharedCore.Stack => Bool)
        (SourceClauseClearExcept.Label
          (SourceClauseClearExcept.workCount PrefixSharedClear.keep))
        (Unit × Option Bool)))
      (UnitHandoff.after_clear n a ordinal w ell sign
        saved output count B)
  obtain ⟨t,ht,h⟩ := BitMachineRawSequence.runs
    (pairProgram a w ell sign) PrefixSharedClear.program
    (BitMachineRawSequence.leftLabel
      (SourceClauseFixedBatch.labelAt
        (UnitStage.constantSize a w ell) 0))
    (.clear 0) ((),PrefixUnitRun.startControl)
    ((),PrefixUnitRun.startControl) ((),none) ((),none)
    B F (PrefixGateReady.blank n ordinal
      (UnitHandoff.nextSaved n a ordinal w ell sign saved)
      output (true :: count))
    u (PrefixSharedClear.cost F) hU hC
  refine ⟨t,?_,h⟩
  change t ≤ pairCost n a ordinal w ell saved output count +
    PrefixSharedClear.cost F + 1
  omega

#print axioms run

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.UnitCycle
