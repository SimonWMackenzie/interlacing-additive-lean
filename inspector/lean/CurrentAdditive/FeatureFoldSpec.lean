import CurrentAdditive.FeatureStepSpec
import EthInapproximability.CurrentPaper.SourceListEncoding

/-!
The exact accumulator invariant for a physical counted-list scheduler.
Start from the old descriptor fields.  Each old descriptor contributes all
alphabet extensions in original alphabet order, or no bytes at depth D.
The resulting fields are exactly the body of the next production packet.
This is the semantic target for a physical callback, not a machine run.
-/

namespace CurrentAdditive.FeatureFoldSpec

open CurrentAdditive.FeatureStepSpec
open CurrentAdditive.CylinderFeatureCodec
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open SequentialCode

private theorem fields_append (xs ys : List (List Bool)) :
    SourceListEncoding.fields (xs ++ ys) =
      SourceListEncoding.fields xs ++ SourceListEncoding.fields ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [SourceListEncoding.fields, ih, List.append_assoc]

def extensionWords (q : Nat) (alphabet : Array Nat)
    (c : List (Nat × Nat)) : List (List Bool) :=
  (alphabet.toList.map (fun y => (q,y)::c)).map encodeFeature

def featureStep (q D : Nat) (alphabet : Array Nat)
    (acc : List Bool) (c : List (Nat × Nat)) : List Bool :=
  acc ++ if c.length < D then
    SourceListEncoding.fields (extensionWords q alphabet c) else []

/-- The callback's exact byte-level input is one V2 feature word. -/
def featureStepBytes (q D : Nat) (alphabet : Array Nat)
    (acc word : List Bool) : List Bool :=
  acc ++ match decodeFeature word with
    | none => []
    | some c => if c.length < D then
        SourceListEncoding.fields (extensionWords q alphabet c) else []

theorem featureStepBytes_canonical (q D : Nat) (alphabet : Array Nat)
    (acc : List Bool) (c : List (Nat × Nat)) :
    featureStepBytes q D alphabet acc (encodeFeature c) =
      featureStep q D alphabet acc c := by
  simp [featureStepBytes, featureStep]

theorem fold_encoded (q D : Nat) (alphabet : Array Nat)
    (xs : List (List (Nat × Nat))) (acc : List Bool) :
    (xs.map encodeFeature).foldl (featureStepBytes q D alphabet) acc =
      xs.foldl (featureStep q D alphabet) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons c cs ih =>
      simp [List.foldl_cons, featureStepBytes_canonical, ih]

theorem fold_extensions (q D : Nat) (alphabet : Array Nat)
    (xs : List (List (Nat × Nat))) (acc0 : List Bool) :
    xs.foldl (featureStep q D alphabet) acc0 =
      acc0 ++ SourceListEncoding.fields
        (((xs.filter (fun c => decide (c.length < D))).flatMap
          (fun c => alphabet.toList.map (fun y => (q,y)::c))).map
            encodeFeature) := by
  induction xs generalizing acc0 with
  | nil => simp [SourceListEncoding.fields]
  | cons c xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      by_cases hc : c.length < D
      · simp [featureStep, hc, extensionWords, fields_append,
          List.append_assoc]
      · simp [featureStep, hc, extensionWords, fields_append,
          List.append_assoc]

theorem step_fields_exact (q D : Nat) (alphabet : Array Nat) :
    (oldFeatures q D alphabet).foldl (featureStep q D alphabet)
      (SourceListEncoding.fields
        ((oldFeatures q D alphabet).map encodeFeature)) =
      SourceListEncoding.fields
        (((generatedFeatures (q+1) D alphabet).toList).map
          encodeFeature) := by
  rw [fold_extensions, FeatureStepSpec.step_features_exact]
  simp only [List.map_append, fields_append]
  rfl

theorem step_packet_from_fields (q D : Nat) (alphabet : Array Nat) :
    generatedFeatureBits (q+1) D alphabet =
      natField
        (generatedFeatures (q+1) D alphabet).size ++
      (oldFeatures q D alphabet).foldl (featureStep q D alphabet)
        (SourceListEncoding.fields
          ((oldFeatures q D alphabet).map encodeFeature)) := by
  rw [step_fields_exact]
  simp [generatedFeatureBits, encodeFeatures,
    CurrentAdditive.CodeDCodecV2.encodeItems,
    SourceListEncoding.encode]

theorem step_packet_from_encoded_fold (q D : Nat)
    (alphabet : Array Nat) :
    generatedFeatureBits (q+1) D alphabet =
      natField (generatedFeatures (q+1) D alphabet).size ++
      ((oldFeatures q D alphabet).map encodeFeature).foldl
        (featureStepBytes q D alphabet)
        (SourceListEncoding.fields
          ((oldFeatures q D alphabet).map encodeFeature)) := by
  rw [fold_encoded]
  exact step_packet_from_fields q D alphabet

#print axioms step_fields_exact
#print axioms step_packet_from_fields
#print axioms step_packet_from_encoded_fold

end CurrentAdditive.FeatureFoldSpec
