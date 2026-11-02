import CurrentAdditive.CodeDTargetV2

/-!
One exact logical stage of the fixed-D physical controller.  The stage uses
the selected source's actual append order, generated feature order, full
materialized rational Gauss routine, minimum-ratio update, zero deletion and
source-size fuel.  These equations are the required correctness target for a
finite-stack implementation.  No physical machine is asserted here.
-/

namespace CurrentAdditive.CodeDStageContractV2

open SequentialCode SequentialSourceCode
open CodeDCanonicalSourceV2 CodeDTargetV2

def extended (q : Nat) (alphabet : Array (Nat × ℚ))
    (prev : Array ((Fin q → Nat) × ℚ)) :
    Array ((Fin (q + 1) → Nat) × ℚ) :=
  appendSource prev alphabet

def features (D q : Nat) (alphabet : Array (Nat × ℚ)) :
    Array (List (Nat × Nat)) :=
  generatedFeatures (q + 1) D (alphabet.map Prod.fst)

def step (D q : Nat) (alphabet : Array (Nat × ℚ))
    (prev : Array ((Fin q → Nat) × ℚ)) :
    Option (Array ((Fin (q + 1) → Nat) × ℚ)) :=
  let source := extended q alphabet prev
  let featureList := features D q alphabet
  let n := featureList.size
  let value : (Fin (q + 1) → Nat) → Fin n → ℚ :=
    fun v j => generatedFeatureValue v featureList[j]
  compressSourceFuelMaterialized n value source source.size

theorem step_is_actual_successor (D q : Nat)
    (alphabet : Array (Nat × ℚ))
    (prev : Array ((Fin q → Nat) × ℚ))
    (hprev : sequentialMaterialized D alphabet q = some prev) :
    step D q alphabet prev = sequentialMaterialized D alphabet (q + 1) := by
  simp [step, extended, features, sequentialMaterialized, hprev]

def stageBytes (D q : Nat) (alphabet : Array (Nat × ℚ))
    (prev : Array ((Fin q → Nat) × ℚ)) : Option (List Bool) :=
  (step D q alphabet prev).map encodedSource

theorem stageBytes_is_target (D q : Nat)
    (alphabet : Array (Nat × ℚ))
    (prev : Array ((Fin q → Nat) × ℚ))
    (hprev : sequentialMaterialized D alphabet q = some prev) :
    stageBytes D q alphabet prev = targetBytes D alphabet (q + 1) := by
  simp [stageBytes, targetBytes, step_is_actual_successor D q alphabet prev hprev]

theorem stageBytes_decodes (D q : Nat)
    (alphabet : Array (Nat × ℚ))
    (prev : Array ((Fin q → Nat) × ℚ))
    (out : Array ((Fin (q + 1) → Nat) × ℚ))
    (hstep : step D q alphabet prev = some out) :
    stageBytes D q alphabet prev = some (encodedSource out) ∧
      CodeDSourceCodecV2.decodeSource (q + 1) (encodedSource out) =
        some (canonicalSource out) := by
  exact ⟨by simp [stageBytes, hstep], decode_encodedSource out⟩

#print axioms step_is_actual_successor
#print axioms stageBytes_is_target
#print axioms stageBytes_decodes

end CurrentAdditive.CodeDStageContractV2
