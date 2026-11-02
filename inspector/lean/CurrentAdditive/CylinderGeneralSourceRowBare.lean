import CurrentAdditive.CylinderGeneralFeatureSemanticBare
import CurrentAdditive.CylinderSourceTupleProjection

/-! Decode each retained V2 tuple word to its actual q-coordinate tuple.
This fixes the semantic output list expected from the pending physical
arbitrary-feature row callback. -/

namespace CurrentAdditive.CylinderGeneralSourceRowBare

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.CylinderSourceTupleProjection
open CurrentAdditive.CylinderGeneralFeatureSemanticBare
open SequentialCode

def tupleOfWord (q : Nat) (word : List Bool) : Fin q → Nat :=
  fun j => bitsValue (((SourceListEncoding.decode word).getD [])[j.val]?.getD [])

theorem tupleOfWord_canonical {q : Nat}
    (entry : (Fin q → Nat) × ℚ) :
    tupleOfWord q
      (SourceListEncoding.encode
        (List.ofFn (fun j : Fin q => (entry.1 j).bits))) = entry.1 := by
  funext j
  simp [tupleOfWord, SourceListEncoding.decode_encode, bitsValue_bits]

def featurePiece (q : Nat) (feature : List (Nat × Nat))
    (word : List Bool) : List Bool :=
  [decide (generatedFeatureValue (tupleOfWord q word) feature ≠ 0)]

theorem featurePiece_canonical {q : Nat}
    (entry : (Fin q → Nat) × ℚ)
    (feature : List (Nat × Nat)) :
    featurePiece q feature
      (SourceListEncoding.encode
        (List.ofFn (fun j : Fin q => (entry.1 j).bits))) =
      [decide (generatedFeatureValue entry.1 feature ≠ 0)] := by
  simp [featurePiece, tupleOfWord_canonical]

theorem feature_row_exact {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (feature : List (Nat × Nat)) :
    (tupleWords source).flatMap (featurePiece q feature) =
      source.toList.map (fun entry =>
        decide (generatedFeatureValue entry.1 feature ≠ 0)) := by
  simp only [tupleWords, List.flatMap_map]
  simp only [featurePiece_canonical]
  exact List.map_eq_flatMap.symm

theorem featurePiece_as_conjunction {q : Nat}
    (entry : (Fin q → Nat) × ℚ)
    (feature : List (Nat × Nat)) :
    featurePiece q feature
      (SourceListEncoding.encode
        (List.ofFn (fun j : Fin q => (entry.1 j).bits))) =
      [CurrentAdditive.CylinderConjunctionMachine.conjunction true
        (comparisonBits entry.1 feature)] := by
  rw [featurePiece_canonical, fold_equals_generated_value]

#print axioms tupleOfWord_canonical
#print axioms feature_row_exact
#print axioms featurePiece_as_conjunction

end CurrentAdditive.CylinderGeneralSourceRowBare
