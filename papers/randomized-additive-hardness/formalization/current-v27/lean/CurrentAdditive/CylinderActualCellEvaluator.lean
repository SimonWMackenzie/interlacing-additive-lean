import CurrentAdditive.CylinderActualFeatureEvaluator
import CurrentAdditive.CylinderEvalTypedBytes
import CurrentAdditive.CylinderEvalReassociateMachine
import CurrentAdditive.CylinderRowSerializer

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace CurrentAdditive.CylinderActualCellEvaluator

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open CurrentAdditive.CylinderFeatureCodec

noncomputable def booleanMachine : BitMachine.Machine :=
  BitMachineComposition.composition CylinderEvalReassociate.machine
    CylinderActualFeatureEvaluator.machine

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition booleanMachine CylinderRowSerializer.cellMachine

def input {q : ℕ} (v : Fin q → ℕ) (feature : List (ℕ × ℕ)) : List Bool :=
  encode ![encode ![List.replicate q true,encodeFeature feature],
    CylinderEvalPairMachine.tupleWord v]

def output {q : ℕ} (v : Fin q → ℕ) (feature : List (ℕ × ℕ)) : List Bool :=
  CylinderRowSerializer.encodedCell
    (decide (SequentialCode.generatedFeatureValue v feature≠0))

noncomputable def clock {q : ℕ} (v : Fin q → ℕ) (feature : List (ℕ × ℕ)) : ℕ :=
  30*((input v feature).length+1)+
    2*(CylinderActualFeatureEvaluator.input v feature).length+2+
    CylinderActualFeatureEvaluator.clock v feature+5

theorem outputs {q : ℕ} (v : Fin q → ℕ) (feature : List (ℕ × ℕ))
    (valid : ∀p∈feature,p.1<q) :
    machine.OutputsWithin (input v feature) (output v feature) (clock v feature) := by
  have hr := CylinderEvalReassociate.outputs (List.replicate q true)
    (encodeFeature feature) (CylinderEvalPairMachine.tupleWord v)
  have he := CylinderActualFeatureEvaluator.outputs v feature valid
  change CylinderEvalReassociate.machine.OutputsWithin (input v feature)
    (CylinderActualFeatureEvaluator.input v feature) (30*((input v feature).length+1)) at hr
  have hb := BitMachineComposition.composition_outputsWithin
    CylinderEvalReassociate.machine CylinderActualFeatureEvaluator.machine hr he
  have hc := CylinderRowSerializer.cell_outputs
    (decide (SequentialCode.generatedFeatureValue v feature≠0))
  have h := BitMachineComposition.composition_outputsWithin
    booleanMachine CylinderRowSerializer.cellMachine hb hc
  simpa only [machine,clock,output,List.length_singleton] using h

end CurrentAdditive.CylinderActualCellEvaluator

#print axioms CurrentAdditive.CylinderActualCellEvaluator.outputs
