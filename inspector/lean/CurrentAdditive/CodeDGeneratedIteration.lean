import CurrentAdditive.CodeDCompressionIteration
import CurrentAdditive.LabelTrace

/-! The fixed-count controller agrees with the actual generated-feature
compression stages. Feature nonemptiness, the constant row and positivity
are derived from the existing constructors, not supplied machine runs. -/
namespace CurrentAdditive.CodeDGeneratedIteration

open CodeDCompressionIteration IndependentSupport SequentialCode SequentialSourceCode
open IntegerBitSupport LabelTrace

theorem generated_iterate_trace {Y : Type*} [DecidableEq Y]
    (q D : Nat) (alphabet : Array Y)
    (source : Array ((Fin q → Y) × ℚ)) (hpositive : SourcePositive source) (t : Nat) :
    let F := generatedFeatures q D alphabet
    ∃ e, e ≤ t ∧ EliminationTrace F.size (fun v j => generatedFeatureValue v F[j]) e
      source ((onePass F.size (fun v j => generatedFeatureValue v F[j]))^[t] source) := by
  exact iterate_trace _ _ (generatedFeatures_pos q D alphabet)
    (generatedFeatures_constant q D alphabet) source hpositive t

theorem generated_source_size_iteration {Y : Type*} [DecidableEq Y]
    (q D : Nat) (alphabet : Array Y)
    (source : Array ((Fin q → Y) × ℚ)) (hpositive : SourcePositive source) :
    let F := generatedFeatures q D alphabet
    compressUntilIndependent F.size (fun v j => generatedFeatureValue v F[j])
      source source.size =
      some ((onePass F.size (fun v j => generatedFeatureValue v F[j]))^[source.size] source) := by
  exact source_size_iteration _ _ (generatedFeatures_pos q D alphabet)
    (generatedFeatures_constant q D alphabet) source hpositive

theorem preprocessed_source_positive {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ)) (q : Nat)
    (prev : Array ((Fin q → Y) × ℚ))
    (hprev : sequentialPreprocessed D alphabet q = some prev) : SourcePositive prev := by
  obtain ⟨other, hother, hp⟩ := sequentialPreprocessed_total D alphabet q
  rw [hprev] at hother
  cases Option.some.inj hother
  exact hp

/-- Every physical controller prefix has an exact pure elimination trace,
including identity padding once the support has become independent. -/
theorem stage_iterate_trace {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ)) (q : Nat)
    (prev : Array ((Fin q → Y) × ℚ))
    (hprev : sequentialPreprocessed D alphabet q = some prev) (t : Nat) :
    let F := generatedFeatures (q+1) D ((positiveLaw alphabet).map Prod.fst)
    let source := appendSource prev (positiveLaw alphabet)
    ∃ e, e ≤ t ∧ EliminationTrace F.size (fun v j => generatedFeatureValue v F[j]) e
      source ((onePass F.size (fun v j => generatedFeatureValue v F[j]))^[t] source) := by
  exact generated_iterate_trace (q+1) D ((positiveLaw alphabet).map Prod.fst)
    (appendSource prev (positiveLaw alphabet))
    (appendSource_positive prev (positiveLaw alphabet)
      (preprocessed_source_positive D alphabet q prev hprev) (positiveLaw_positive alphabet)) t

theorem stage_iterate_positive {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ)) (q : Nat)
    (prev : Array ((Fin q → Y) × ℚ))
    (hprev : sequentialPreprocessed D alphabet q = some prev) (t : Nat) :
    let F := generatedFeatures (q+1) D ((positiveLaw alphabet).map Prod.fst)
    let source := appendSource prev (positiveLaw alphabet)
    SourcePositive ((onePass F.size (fun v j => generatedFeatureValue v F[j]))^[t] source) := by
  exact iterate_positive _ _ (generatedFeatures_pos _ _ _)
    (generatedFeatures_constant _ _ _)
    (appendSource prev (positiveLaw alphabet))
    (appendSource_positive prev (positiveLaw alphabet)
      (preprocessed_source_positive D alphabet q prev hprev) (positiveLaw_positive alphabet)) t

/-- The controller's initial candidate-count iterations equal the existing
next-stage constructor. No successful controller or physical-run premise is used. -/
theorem stage_source_size_iteration {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ)) (q : Nat)
    (prev : Array ((Fin q → Y) × ℚ))
    (hprev : sequentialPreprocessed D alphabet q = some prev) :
    let F := generatedFeatures (q+1) D ((positiveLaw alphabet).map Prod.fst)
    let source := appendSource prev (positiveLaw alphabet)
    sequentialPreprocessed D alphabet (q+1) =
      some ((onePass F.size (fun v j => generatedFeatureValue v F[j]))^[source.size] source) := by
  have h := generated_source_size_iteration (q+1) D ((positiveLaw alphabet).map Prod.fst)
    (appendSource prev (positiveLaw alphabet))
    (appendSource_positive prev (positiveLaw alphabet)
      (preprocessed_source_positive D alphabet q prev hprev) (positiveLaw_positive alphabet))
  have hp : sequentialIndependent D (positiveLaw alphabet) q = some prev := hprev
  simpa [sequentialPreprocessed, sequentialIndependent, hp] using h

#print axioms generated_iterate_trace
#print axioms generated_source_size_iteration
#print axioms stage_iterate_trace
#print axioms stage_source_size_iteration

end CurrentAdditive.CodeDGeneratedIteration
