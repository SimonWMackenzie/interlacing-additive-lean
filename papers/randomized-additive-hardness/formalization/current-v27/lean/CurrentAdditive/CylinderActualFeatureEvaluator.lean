import CurrentAdditive.FeatureContextMapExplicit
import CurrentAdditive.CylinderEvalPairPolynomial
import CurrentAdditive.CylinderEvalConjunction
import EthInapproximability.CurrentPaper.BitMachineComposition

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

/-! A descriptor is evaluated by physically running every actual pair test
and then the literal conjunction program. No comparison bits are input data.
-/

namespace CurrentAdditive.CylinderActualFeatureEvaluator

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open CurrentAdditive.CylinderFeatureCodec CurrentAdditive.CylinderGeneralFeatureSemanticBare
open CurrentAdditive.FeatureMapPairLoader

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition
    (FeatureContextMap.machine CylinderEvalPairMachine.machine false)
    CylinderEvalConjunction.machine

def pairItems (feature : List (ℕ × ℕ)) : List (List Bool) := feature.map encodePair

def pairResult {q : ℕ} (v : Fin q → ℕ) (word : List Bool) : List Bool :=
  [pairMatches v ((decodePair word).getD (0,0))]

def pairClock {q : ℕ} (v : Fin q → ℕ) (word : List Bool) : ℕ :=
  128*((packet (CylinderEvalPairMachine.context v) word).length+1)^3

theorem pair_runs {q : ℕ} (v : Fin q → ℕ) (feature : List (ℕ × ℕ))
    (valid : ∀ p∈feature,p.1<q) :
    ∀ word∈pairItems feature,CylinderEvalPairMachine.machine.OutputsWithin
      (packet (CylinderEvalPairMachine.context v) word) (pairResult v word) (pairClock v word) := by
  intro word hw
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hw
  simpa only [pairResult,decodePair_encodePair,Option.getD_some,pairClock,packet] using
    CylinderEvalPairMachine.contextual_outputs v p (valid p hp)

def input {q : ℕ} (v : Fin q → ℕ) (feature : List (ℕ × ℕ)) : List Bool :=
  packet (CylinderEvalPairMachine.context v) (encodeFeature feature)

theorem raw_input {q : ℕ} (v : Fin q → ℕ) (feature : List (ℕ × ℕ)) :
    packet (CylinderEvalPairMachine.context v) (SourceListEncoding.encode (pairItems feature))=
      input v feature := rfl

theorem comparison_result {q : ℕ} (v : Fin q → ℕ) (feature : List (ℕ × ℕ)) :
    FeatureContextMap.result false (pairItems feature) (pairResult v)=comparisonBits v feature := by
  simp only [FeatureContextMap.result,Bool.false_eq_true,↓reduceIte,pairItems,List.flatMap_map]
  simp only [pairResult,decodePair_encodePair,Option.getD_some]
  exact List.map_eq_flatMap.symm

noncomputable def mapClock {q : ℕ} (v : Fin q → ℕ) (feature : List (ℕ × ℕ)) : ℕ :=
  FeatureContextMap.totalBudget CylinderEvalPairMachine.machine false
    (CylinderEvalPairMachine.context v) (pairItems feature) (pairResult v) (pairClock v)

noncomputable def clock {q : ℕ} (v : Fin q → ℕ) (feature : List (ℕ × ℕ)) : ℕ :=
  mapClock v feature+2*(comparisonBits v feature).length+2+
    ((comparisonBits v feature).length+1)

theorem outputs {q : ℕ} (v : Fin q → ℕ) (feature : List (ℕ × ℕ))
    (valid : ∀ p∈feature,p.1<q) :
    machine.OutputsWithin (input v feature)
      [decide (SequentialCode.generatedFeatureValue v feature≠0)] (clock v feature) := by
  have hm := FeatureContextMap.outputs_explicit CylinderEvalPairMachine.machine false
    (CylinderEvalPairMachine.context v) (pairItems feature) (pairResult v) (pairClock v)
    (pair_runs v feature valid)
  rw [raw_input,comparison_result] at hm
  have hc := CylinderEvalConjunction.outputs (comparisonBits v feature)
  have h := BitMachineComposition.composition_outputsWithin
    (FeatureContextMap.machine CylinderEvalPairMachine.machine false)
    CylinderEvalConjunction.machine hm hc
  rw [fold_equals_generated_value] at h
  exact h

end CurrentAdditive.CylinderActualFeatureEvaluator

#print axioms CurrentAdditive.CylinderActualFeatureEvaluator.outputs
