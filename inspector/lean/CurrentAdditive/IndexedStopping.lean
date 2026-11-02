import CurrentAdditive.IndexedInjection

namespace CurrentAdditive.IndexedLaw

open SequentialCode SequentialSourceCode SequentialFeatureCoverage
  IndependentSupport LabelTrace

theorem compressUntilIndependent_stopped {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ)) (fuel : Nat)
    (h : compressUntilIndependent n φ source fuel = some out) :
    sourceFreeColumn n φ out = none := by
  induction fuel generalizing source with
  | zero =>
      cases hf : sourceFreeColumn n φ source with
      | none =>
          simp [compressUntilIndependent, hf] at h
          cases h
          exact hf
      | some f => simp [compressUntilIndependent, hf] at h
  | succ fuel ih =>
      cases hf : sourceFreeColumn n φ source with
      | none =>
          simp [compressUntilIndependent, hf] at h
          cases h
          exact hf
      | some f =>
          cases hs : compressSourceOnceMaterialized n φ source with
          | none => simp [compressUntilIndependent, hf, hs] at h
          | some next =>
              simp [compressUntilIndependent, hf, hs] at h
              exact ih next h

/-- Every completed nonempty-word stage exits precisely when its actual
first-free-column scan says that no dependence remains. -/
theorem construct_stopped {m : Nat} (D : Nat) (μ : Fin m → ℚ) (q : Nat) :
    sourceFreeColumn
      (generatedFeatures (q + 1) D
        ((positiveLaw (indexedAlphabet μ)).map Prod.fst)).size
      (fun v j => generatedFeatureValue v
        (generatedFeatures (q + 1) D
          ((positiveLaw (indexedAlphabet μ)).map Prod.fst))[j])
      (construct D μ (q + 1)) = none := by
  have h := construct_run D μ (q + 1)
  simp only [sequentialIndependent] at h
  cases hp : sequentialIndependent D (positiveLaw (indexedAlphabet μ)) q with
  | none => simp [hp] at h
  | some prev =>
      simp [hp] at h
      exact compressUntilIndependent_stopped _ _ _ _ _ h

#print axioms construct_success
#print axioms construct_cylinder
#print axioms construct_isDWise
#print axioms codeSource
#print axioms construct_independent
#print axioms construct_word_injective
#print axioms tupleEmbedding
#print axioms construct_stopped

end CurrentAdditive.IndexedLaw
