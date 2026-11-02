import CurrentAdditive.CylinderFeatureCodec
import CurrentAdditive.CylinderPreparedMatrixBridge
import CurrentAdditive.SequentialFeatureCount

/-!
The exact loop target for the physical cylinder generator.  At coordinate `j`,
the previous feature packet is copied first.  For each eligible previous
feature, the alphabet is scanned in its original order and `(j,y)` is
prepended.  This list specification fixes duplicate indices and framing for
the pending finite-stack loop; it is not itself a physical producer.
-/

namespace CurrentAdditive.CylinderOrderedSpec

open EthInapproximability.CurrentPaper
open SequentialCode
open CurrentAdditive.CylinderFeatureCodec

def extendList (D j : Nat) (alphabet : List Nat)
    (old : List (List (Nat × Nat))) : List (List (Nat × Nat)) :=
  old ++ (old.filter (fun c => decide (c.length < D))).flatMap
    (fun c => alphabet.map (fun y => (j, y) :: c))

private theorem fold_append_eq_flatMap {α β : Type*} (xs : List α)
    (f : α → Array β) (out : Array β) :
    xs.foldl (fun a x => a ++ f x) out =
      out ++ (xs.flatMap fun x => (f x).toList).toArray := by
  induction xs generalizing out with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.flatMap_cons]
      rw [ih]
      have h : f x ++ (List.flatMap (fun x => (f x).toList) xs).toArray =
          ((f x).toList ++ List.flatMap (fun x => (f x).toList) xs).toArray :=
        Array.toList_inj.mp (by simp [Array.toList_append])
      simpa only [Array.append_assoc] using congrArg (fun z => out ++ z) h

theorem extendList_exact (D j : Nat) (alphabet : Array Nat)
    (old : Array (List (Nat × Nat))) :
    (extendFeatures D alphabet j old).toList =
      extendList D j alphabet.toList old.toList := by
  unfold extendFeatures extendList
  rw [Array.toList_append]
  rw [← Array.foldl_toList]
  rw [fold_append_eq_flatMap]
  simp [Array.toList_map]

def generatedList (q D : Nat) (alphabet : List Nat) :
    List (List (Nat × Nat)) :=
  (List.range q).foldl (fun old j => extendList D j alphabet old) [[]]

theorem generatedList_exact (q D : Nat) (alphabet : Array Nat) :
    generatedList q D alphabet.toList =
      (generatedFeatures q D alphabet).toList := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [SequentialFeatureCoverage.generatedFeatures_succ]
      simp only [generatedList, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      rw [← generatedList, ih]
      exact (extendList_exact D q alphabet
        (generatedFeatures q D alphabet)).symm

def featurePacket (q D : Nat) (alphabet : Array Nat) : List Bool :=
  CodeDCodecV2.encodeItems
    ((generatedList q D alphabet.toList).map encodeFeature)

theorem featurePacket_exact (q D : Nat) (alphabet : Array Nat) :
    featurePacket q D alphabet = generatedFeatureBits q D alphabet := by
  simp [featurePacket, generatedFeatureBits, encodeFeatures,
    generatedList_exact]

theorem featurePacket_decodes (q D : Nat) (alphabet : Array Nat) :
    CodeDCodecV2.decodeItems (featurePacket q D alphabet) =
      some ((generatedFeatures q D alphabet).toList.map encodeFeature) := by
  rw [featurePacket_exact]
  exact generatedFeatureBits_order q D alphabet

def rowBits {q : Nat} (feature : List (Nat × Nat))
    (source : Array ((Fin q → Nat) × ℚ)) : List Bool :=
  source.toList.map (fun entry =>
    decide (generatedFeatureValue entry.1 feature ≠ 0))

def streamedRows (q D : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ)) : List (List Bool) :=
  (generatedList q D alphabet.toList).map (fun feature => rowBits feature source)

theorem cylinder_rows_are_feature_map (q D : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ)) :
    cylinders q D alphabet source =
      (generatedFeatures q D alphabet).map (fun feature =>
        source.map (fun entry => generatedFeatureValue entry.1 feature)) := by
  apply Array.ext
  · simp [cylinders, featureRows]
  · intro i hi₁ hi₂
    simp [cylinders, featureRows]

theorem streamedRows_prepared (q D : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ)) :
    streamedRows q D alphabet source =
      CurrentAdditive.CylinderPreparedMatrixBridge.preparedRows q D alphabet source := by
  unfold CurrentAdditive.CylinderPreparedMatrixBridge.preparedRows
  rw [cylinder_rows_are_feature_map]
  simp [streamedRows, rowBits, ← generatedList_exact, List.map_map]

theorem streamedRows_encoding (q D : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ)) :
    CurrentAdditive.CylinderMatrixSerializer.encodedMatrix
        (streamedRows q D alphabet source) =
      cylinderMatrixBits q D alphabet source := by
  rw [streamedRows_prepared]
  exact CurrentAdditive.CylinderPreparedMatrixBridge.preparedRows_encoding
    q D alphabet source

theorem matrix_shape (q D : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ)) :
    (cylinders q D alphabet source).size =
      (generatedList q D alphabet.toList).length ∧
    (∀ i, i < (cylinders q D alphabet source).size →
      ((cylinders q D alphabet source)[i]?.getD #[]).size = source.size) := by
  constructor
  · rw [cylinders_rows]
    have h := congrArg List.length (generatedList_exact q D alphabet)
    simpa using h.symm
  · intro i hi
    simpa [Array.getElem?_eq_getElem hi] using
      cylinders_columns q D alphabet source i hi

#print axioms featurePacket_decodes
#print axioms streamedRows_encoding
#print axioms matrix_shape

end CurrentAdditive.CylinderOrderedSpec
