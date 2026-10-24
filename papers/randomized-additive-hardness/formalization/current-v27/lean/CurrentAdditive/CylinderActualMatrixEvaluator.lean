import CurrentAdditive.CylinderActualRowEvaluator
import CurrentAdditive.CylinderPreparedReassociate

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

/-! A fixed physical machine for the prepared cylinder matrix packet. Every
entry is computed from an actual feature descriptor and an actual tuple.
The generated feature and tuple lists are traversed in their encoded order. -/

namespace CurrentAdditive.CylinderActualMatrixEvaluator

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open CurrentAdditive.CylinderFeatureCodec CurrentAdditive.CylinderEvalTypedBytes
open CurrentAdditive.FeatureMapPairLoader

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition CylinderPreparedReassociate.machine
    (FeatureContextMap.machine CylinderActualRowEvaluator.machine true)

def context {q : ℕ} (source : Array ((Fin q → ℕ) × ℚ)) : List Bool :=
  encode ![List.replicate q true,
    SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)]

def featureItems (q D : ℕ) (alphabet : Array ℕ) : List (List Bool) :=
  (SequentialCode.generatedFeatures q D alphabet).toList.map encodeFeature

def rowResult {q : ℕ} (source : Array ((Fin q → ℕ) × ℚ))
    (word : List Bool) : List Bool :=
  CylinderActualRowEvaluator.output (featureValue word) source

noncomputable def rowClock {q : ℕ} (source : Array ((Fin q → ℕ) × ℚ))
    (word : List Bool) : ℕ :=
  CylinderActualRowEvaluator.clock (featureValue word) source

theorem row_runs (q D : ℕ) (alphabet : Array ℕ)
    (source : Array ((Fin q → ℕ) × ℚ)) :
    ∀ word∈featureItems q D alphabet,
      CylinderActualRowEvaluator.machine.OutputsWithin
        (packet (context source) word) (rowResult source word) (rowClock source word) := by
  intro word hw
  obtain ⟨feature,hf,rfl⟩ := List.mem_map.mp hw
  have hv := generated_features_valid q D alphabet feature hf
  have hrun := CylinderActualRowEvaluator.outputs feature source hv
  simpa only [rowResult,rowClock,featureValue_encodeFeature,context,packet,
    CylinderActualRowEvaluator.input] using hrun

def input (q D : ℕ) (alphabet : Array ℕ)
    (source : Array ((Fin q → ℕ) × ℚ)) : List Bool :=
  encode ![List.replicate q true,generatedFeatureBits q D alphabet,
    SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)]

def routedInput (q D : ℕ) (alphabet : Array ℕ)
    (source : Array ((Fin q → ℕ) × ℚ)) : List Bool :=
  packet (context source) (SourceListEncoding.encode (featureItems q D alphabet))

theorem feature_items_bytes (q D : ℕ) (alphabet : Array ℕ) :
    SourceListEncoding.encode (featureItems q D alphabet)=generatedFeatureBits q D alphabet := rfl

theorem matrix_result (q D : ℕ) (alphabet : Array ℕ)
    (source : Array ((Fin q → ℕ) × ℚ)) :
    FeatureContextMap.result true (featureItems q D alphabet) (rowResult source)=
      cylinderMatrixBits q D alphabet source := by
  rw [← CylinderOrderedSpec.streamedRows_encoding]
  simp [FeatureContextMap.result,featureItems,rowResult,
    CylinderActualRowEvaluator.output,CylinderMatrixSerializer.encodedMatrix,
    CylinderOrderedSpec.streamedRows,CylinderOrderedSpec.generatedList_exact,List.map_map,Function.comp_def]

noncomputable def mapClock (q D : ℕ) (alphabet : Array ℕ)
    (source : Array ((Fin q → ℕ) × ℚ)) : ℕ :=
  FeatureContextMap.totalBudget CylinderActualRowEvaluator.machine true
    (context source) (featureItems q D alphabet) (rowResult source) (rowClock source)

noncomputable def clock (q D : ℕ) (alphabet : Array ℕ)
    (source : Array ((Fin q → ℕ) × ℚ)) : ℕ :=
  30*((input q D alphabet source).length+1)+
    2*(routedInput q D alphabet source).length+2+mapClock q D alphabet source

theorem outputs (q D : ℕ) (alphabet : Array ℕ)
    (source : Array ((Fin q → ℕ) × ℚ)) :
    machine.OutputsWithin (input q D alphabet source)
      (cylinderMatrixBits q D alphabet source) (clock q D alphabet source) := by
  have hm := FeatureContextMap.outputs_explicit CylinderActualRowEvaluator.machine true
    (context source) (featureItems q D alphabet) (rowResult source) (rowClock source)
    (row_runs q D alphabet source)
  rw [matrix_result] at hm
  have hr := CylinderPreparedReassociate.outputs (List.replicate q true)
    (generatedFeatureBits q D alphabet)
    (SourceListEncoding.encode (CylinderProductionProjection.tupleWords source))
  change CylinderPreparedReassociate.machine.OutputsWithin (input q D alphabet source)
    (routedInput q D alphabet source) (30*((input q D alphabet source).length+1)) at hr
  exact BitMachineComposition.composition_outputsWithin
    CylinderPreparedReassociate.machine
    (FeatureContextMap.machine CylinderActualRowEvaluator.machine true) hr hm

theorem prepared_outputs (q : ℕ) (alphabet : Array (ℕ × ℚ))
    (source : Array ((Fin q → ℕ) × ℚ)) :
    machine.OutputsWithin
      (encode ![List.replicate q true,generatedFeatureBits q 8192 (alphabet.map Prod.fst),
        SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)])
      (cylinderMatrixBits q 8192 (alphabet.map Prod.fst) source)
      (clock q 8192 (alphabet.map Prod.fst) source) :=
  outputs q 8192 (alphabet.map Prod.fst) source

end CurrentAdditive.CylinderActualMatrixEvaluator

#print axioms CurrentAdditive.CylinderActualMatrixEvaluator.outputs
#print axioms CurrentAdditive.CylinderActualMatrixEvaluator.prepared_outputs
