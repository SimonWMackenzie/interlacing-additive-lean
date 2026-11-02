import CurrentAdditive.CylinderEvalPairPolynomial
import CurrentAdditive.CylinderProductionProjection
import CurrentAdditive.CylinderOrderedSpec

/-! Semantic decoding used only to state the outputs of fixed physical
machines. These definitions neither install a bank nor execute an evaluator. -/

namespace CurrentAdditive.CylinderEvalTypedBytes

open EthInapproximability.CurrentPaper
open CurrentAdditive.CylinderFeatureCodec

def tupleValue (q : ℕ) (word : List Bool) : Fin q → ℕ :=
  fun i => EncodedCommunication.bitsValue
    (((SourceListEncoding.decode word).getD []).getD i.val [])

@[simp] theorem tupleValue_tupleWord {q : ℕ} (v : Fin q → ℕ) :
    tupleValue q (CylinderEvalPairMachine.tupleWord v) = v := by
  funext i
  simp [tupleValue,CylinderEvalPairMachine.tupleWord,SourceListEncoding.decode_encode]

def featureValue (word : List Bool) : List (ℕ × ℕ) :=
  (decodeFeature word).getD []

@[simp] theorem featureValue_encodeFeature (feature : List (ℕ × ℕ)) :
    featureValue (encodeFeature feature) = feature := by
  simp [featureValue]

theorem tupleWords_eq {q : ℕ} (source : Array ((Fin q → ℕ) × ℚ)) :
    CylinderProductionProjection.tupleWords source =
      source.toList.map (fun entry => CylinderEvalPairMachine.tupleWord entry.1) := rfl

theorem tuple_mem {q : ℕ} (source : Array ((Fin q → ℕ) × ℚ))
    (word : List Bool) (hw : word∈CylinderProductionProjection.tupleWords source) :
    ∃ v : Fin q → ℕ, word=CylinderEvalPairMachine.tupleWord v := by
  obtain ⟨entry,_,he⟩ := List.mem_map.mp hw
  exact ⟨entry.1,he.symm⟩

theorem generated_features_valid (q D : ℕ) (alphabet : Array ℕ)
    (feature : List (ℕ × ℕ))
    (hf : feature∈(SequentialCode.generatedFeatures q D alphabet).toList) :
    ∀ p∈feature,p.1<q :=
  CylinderGeneralFeatureSemanticBare.generated_pair_index_valid q D alphabet feature hf

end CurrentAdditive.CylinderEvalTypedBytes

#print axioms CurrentAdditive.CylinderEvalTypedBytes.tupleValue_tupleWord
#print axioms CurrentAdditive.CylinderEvalTypedBytes.tuple_mem
