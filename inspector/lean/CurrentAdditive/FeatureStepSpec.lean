import CurrentAdditive.CylinderFeatureCodec
import CurrentAdditive.SequentialFeatureCoverage

/-!
Exact one-coordinate byte specification for a future physical feature stage.
The previous descriptor packet is the prefix; the suffix scans old features
first, then alphabet entries.  This is a semantic target, not a machine run.
-/

namespace CurrentAdditive.FeatureStepSpec

open CurrentAdditive.CylinderFeatureCodec
open SequentialCode

def oldFeatures (q D : Nat) (alphabet : Array Nat) :
    List (List (Nat × Nat)) :=
  (generatedFeatures q D alphabet).toList

def newFeatures (q D : Nat) (alphabet : Array Nat) :
    List (List (Nat × Nat)) :=
  ((oldFeatures q D alphabet).filter (fun c => decide (c.length < D))).flatMap
    (fun c => alphabet.toList.map (fun y => (q,y)::c))

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

theorem step_features_exact (q D : Nat) (alphabet : Array Nat) :
    (generatedFeatures (q+1) D alphabet).toList =
      oldFeatures q D alphabet ++ newFeatures q D alphabet := by
  rw [CurrentAdditive.SequentialFeatureCoverage.generatedFeatures_succ]
  unfold SequentialCode.extendFeatures oldFeatures newFeatures
  rw [Array.toList_append, ← Array.foldl_toList, fold_append_eq_flatMap]
  simp [oldFeatures, Array.toList_map]

theorem step_packet_exact (q D : Nat) (alphabet : Array Nat) :
    generatedFeatureBits (q+1) D alphabet =
      CurrentAdditive.CodeDCodecV2.encodeItems
        ((oldFeatures q D alphabet).map encodeFeature ++
          (newFeatures q D alphabet).map encodeFeature) := by
  simp only [generatedFeatureBits, encodeFeatures, step_features_exact,
    List.map_append, CurrentAdditive.CodeDCodecV2.encodeItems]

theorem step_feature_count (q D : Nat) (alphabet : Array Nat) :
    (generatedFeatures (q+1) D alphabet).size =
      (oldFeatures q D alphabet).length +
      ((oldFeatures q D alphabet).filter
        (fun c => decide (c.length < D))).length * alphabet.size := by
  rw [← Array.length_toList, step_features_exact]
  simp only [List.length_append, newFeatures, List.length_flatMap]
  simp

#print axioms step_features_exact
#print axioms step_packet_exact
#print axioms step_feature_count

end CurrentAdditive.FeatureStepSpec
