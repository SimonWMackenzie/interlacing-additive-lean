import CurrentAdditive.CylinderActualCellEvaluator

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace CurrentAdditive.CylinderActualRowEvaluator

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open CurrentAdditive.CylinderFeatureCodec CurrentAdditive.CylinderEvalTypedBytes
open CurrentAdditive.FeatureMapPairLoader

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition CylinderEvalReassociate.machine
    (FeatureContextMap.machine CylinderActualCellEvaluator.machine true)

def context (q : ℕ) (feature : List (ℕ × ℕ)) : List Bool :=
  encode ![List.replicate q true,encodeFeature feature]

def cellResult (q : ℕ) (feature : List (ℕ × ℕ)) (word : List Bool) : List Bool :=
  CylinderActualCellEvaluator.output (tupleValue q word) feature

noncomputable def cellClock (q : ℕ) (feature : List (ℕ × ℕ)) (word : List Bool) : ℕ :=
  CylinderActualCellEvaluator.clock (tupleValue q word) feature

theorem cell_runs {q : ℕ} (feature : List (ℕ × ℕ))
    (source : Array ((Fin q → ℕ) × ℚ)) (valid : ∀p∈feature,p.1<q) :
    ∀ word∈CylinderProductionProjection.tupleWords source,
      CylinderActualCellEvaluator.machine.OutputsWithin
        (packet (context q feature) word) (cellResult q feature word)
        (cellClock q feature word) := by
  intro word hw
  obtain ⟨v,rfl⟩ := tuple_mem source word hw
  simpa only [cellResult,cellClock,tupleValue_tupleWord,context,packet,
    CylinderActualCellEvaluator.input] using
    CylinderActualCellEvaluator.outputs v feature valid

def input {q : ℕ} (feature : List (ℕ × ℕ))
    (source : Array ((Fin q → ℕ) × ℚ)) : List Bool :=
  encode ![encode ![List.replicate q true,
    SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)],encodeFeature feature]

def routedInput {q : ℕ} (feature : List (ℕ × ℕ))
    (source : Array ((Fin q → ℕ) × ℚ)) : List Bool :=
  packet (context q feature)
    (SourceListEncoding.encode (CylinderProductionProjection.tupleWords source))

def output {q : ℕ} (feature : List (ℕ × ℕ))
    (source : Array ((Fin q → ℕ) × ℚ)) : List Bool :=
  CylinderRowSerializer.encodedRow (CylinderOrderedSpec.rowBits feature source)

theorem row_result {q : ℕ} (feature : List (ℕ × ℕ))
    (source : Array ((Fin q → ℕ) × ℚ)) :
    FeatureContextMap.result true (CylinderProductionProjection.tupleWords source)
      (cellResult q feature) = output feature source := by
  simp [FeatureContextMap.result,tupleWords_eq,cellResult,output,
    CylinderActualCellEvaluator.output,CylinderOrderedSpec.rowBits,
    CylinderRowSerializer.encodedRow,List.map_map,Function.comp_def]

noncomputable def mapClock {q : ℕ} (feature : List (ℕ × ℕ))
    (source : Array ((Fin q → ℕ) × ℚ)) : ℕ :=
  FeatureContextMap.totalBudget CylinderActualCellEvaluator.machine true
    (context q feature) (CylinderProductionProjection.tupleWords source)
    (cellResult q feature) (cellClock q feature)

noncomputable def clock {q : ℕ} (feature : List (ℕ × ℕ))
    (source : Array ((Fin q → ℕ) × ℚ)) : ℕ :=
  30*((input feature source).length+1)+2*(routedInput feature source).length+2+
    mapClock feature source

theorem outputs {q : ℕ} (feature : List (ℕ × ℕ))
    (source : Array ((Fin q → ℕ) × ℚ)) (valid : ∀p∈feature,p.1<q) :
    machine.OutputsWithin (input feature source) (output feature source)
      (clock feature source) := by
  have hm := FeatureContextMap.outputs_explicit CylinderActualCellEvaluator.machine true
    (context q feature) (CylinderProductionProjection.tupleWords source)
    (cellResult q feature) (cellClock q feature) (cell_runs feature source valid)
  rw [row_result] at hm
  have hr := CylinderEvalReassociate.outputs (List.replicate q true)
    (SourceListEncoding.encode (CylinderProductionProjection.tupleWords source))
    (encodeFeature feature)
  change CylinderEvalReassociate.machine.OutputsWithin (input feature source)
    (routedInput feature source) (30*((input feature source).length+1)) at hr
  exact BitMachineComposition.composition_outputsWithin
    CylinderEvalReassociate.machine
    (FeatureContextMap.machine CylinderActualCellEvaluator.machine true) hr hm

end CurrentAdditive.CylinderActualRowEvaluator

#print axioms CurrentAdditive.CylinderActualRowEvaluator.outputs
