import CurrentAdditive.CylinderFeatureCodec
import CurrentAdditive.CylinderConjunctionMachine
import CurrentAdditive.SequentialFeatureCoverage

/-! The Boolean interpretation of an arbitrary ordered feature descriptor in
the same bare-import environment as the physical coordinate callback. -/

namespace CurrentAdditive.CylinderGeneralFeatureSemanticBare

open EthInapproximability.CurrentPaper
open CurrentAdditive.CylinderFeatureCodec
open SequentialCode

def pairMatches {q : Nat} (v : Fin q → Nat) (p : Nat × Nat) : Bool :=
  if h : p.1 < q then decide (v ⟨p.1, h⟩ = p.2) else false

def comparisonBits {q : Nat} (v : Fin q → Nat)
    (feature : List (Nat × Nat)) : List Bool :=
  feature.map (pairMatches v)

theorem descriptor_bytes (feature : List (Nat × Nat)) :
    encodeFeature feature =
      SourceListEncoding.encode (feature.map encodePair) := rfl

theorem descriptor_decodes (feature : List (Nat × Nat)) :
    SourceListEncoding.decode (encodeFeature feature) =
      some (feature.map encodePair) := by
  simpa only [descriptor_bytes] using
    SourceListEncoding.decode_encode (feature.map encodePair)

theorem pair_record_decodes (p : Nat × Nat) :
    decodePair (encodePair p) = some p := decodePair_encodePair p

theorem fold_comparisons {q : Nat} (v : Fin q → Nat)
    (feature : List (Nat × Nat)) (initial : Bool) :
    CurrentAdditive.CylinderConjunctionMachine.conjunction initial
      (comparisonBits v feature) =
      (initial && feature.all (pairMatches v)) := by
  induction feature generalizing initial with
  | nil => simp [CurrentAdditive.CylinderConjunctionMachine.conjunction,
      comparisonBits]
  | cons p ps ih =>
      simp only [comparisonBits, List.map_cons,
        CurrentAdditive.CylinderConjunctionMachine.conjunction,
        List.foldl_cons, List.all_cons]
      change CurrentAdditive.CylinderConjunctionMachine.conjunction
        (initial && pairMatches v p) (comparisonBits v ps) = _
      rw [ih]
      cases initial <;> cases pairMatches v p <;> simp

theorem fold_equals_generated_value {q : Nat} (v : Fin q → Nat)
    (feature : List (Nat × Nat)) :
    CurrentAdditive.CylinderConjunctionMachine.conjunction true
      (comparisonBits v feature) =
      decide (generatedFeatureValue v feature ≠ 0) := by
  rw [fold_comparisons]
  simp only [Bool.true_and]
  change feature.all (pairMatches v) =
    decide ((if feature.all (pairMatches v) then (1 : ℚ) else 0) ≠ 0)
  cases feature.all (pairMatches v) <;> simp

theorem empty_feature_true {q : Nat} (v : Fin q → Nat) :
    CurrentAdditive.CylinderConjunctionMachine.conjunction true
      (comparisonBits v []) = true := rfl

theorem generated_pair_index_valid (q D : Nat) (alphabet : Array Nat)
    (feature : List (Nat × Nat))
    (hfeature : feature ∈ (generatedFeatures q D alphabet).toList)
    (p : Nat × Nat) (hp : p ∈ feature) : p.1 < q :=
  CurrentAdditive.SequentialFeatureCoverage.generatedFeatures_valid
    q D alphabet feature hfeature p hp

#print axioms descriptor_decodes
#print axioms pair_record_decodes
#print axioms fold_equals_generated_value
#print axioms empty_feature_true
#print axioms generated_pair_index_valid

end CurrentAdditive.CylinderGeneralFeatureSemanticBare
