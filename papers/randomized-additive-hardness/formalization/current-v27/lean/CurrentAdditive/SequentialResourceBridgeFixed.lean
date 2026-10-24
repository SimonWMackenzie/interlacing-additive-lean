import CurrentAdditive.SequentialFeatureCount

/-! Closed-form resource bounds for the literal indexed rational source. -/

namespace CurrentAdditive.SequentialResourceBridgeFixed

open SequentialCode SequentialSourceCode SequentialSourceResource
  SequentialFeatureCount SequentialFiniteLaw

theorem sequentialMaterializedCount_le_dimension {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ)) (q : Nat)
    (out : Array ((Fin q → Y) × ℚ)) (count : Nat)
    (h : sequentialMaterializedCount D alphabet q = some (out, count)) :
    count ≤ q * alphabet.size *
      (∑ k ∈ Finset.range (min D q + 1),
        q.choose k * alphabet.size ^ k) := by
  have hle := sequentialMaterializedCount_le D alphabet q out count h
  rw [generatedFeatures_size_min] at hle
  simpa using hle

theorem sequentialMaterializedCount_total {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ))
    (hpositive : SourcePositive alphabet) (q : Nat) :
    ∃ (out : Array ((Fin q → Y) × ℚ)) (count : Nat),
      sequentialMaterializedCount D alphabet q = some (out, count) ∧
      SourcePositive out ∧
      out.size ≤ (∑ k ∈ Finset.range (min D q + 1),
        q.choose k * alphabet.size ^ k) ∧
      count ≤ q * alphabet.size *
        (∑ k ∈ Finset.range (min D q + 1),
          q.choose k * alphabet.size ^ k) := by
  obtain ⟨out, hout, houtpositive, hsize⟩ :=
    sequentialMaterialized_exists_bounded D alphabet hpositive q
  have heq := sequentialMaterializedCount_iff D alphabet q
  cases hcount : sequentialMaterializedCount D alphabet q with
  | none =>
      rw [hcount] at heq
      simp at heq
      rw [← heq] at hout
      cases hout
  | some p =>
      cases p with
      | mk result count =>
          rw [hcount] at heq
          simp only [Option.map_some] at heq
          rw [hout] at heq
          have hresult : result = out := Option.some.inj heq
          subst result
          refine ⟨out, count, rfl, houtpositive, ?_, ?_⟩
          · rw [generatedFeatures_size_min] at hsize
            simpa using hsize
          · exact sequentialMaterializedCount_le_dimension D alphabet q out count hcount

#print axioms sequentialMaterializedCount_le_dimension
#print axioms sequentialMaterializedCount_total

end CurrentAdditive.SequentialResourceBridgeFixed
