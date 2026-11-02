import CurrentAdditive.MaterializedStepBound

set_option maxHeartbeats 1000000

namespace CurrentAdditive.RationalCandidateCompletion

open CurrentAdditive.SequentialCode
open CurrentAdditive.SequentialZeroDeletion
open CurrentAdditive.RationalBitBounds

/-- Every physical output entry after zero deletion carries the updated
weight at one of the original array indices. No decoded labels are merged. -/
theorem retainedSource_weight_from_updated {α : Type*}
    (source : Array (α × ℚ)) (updated : Array ℚ)
    (j : Fin (retainedSource source updated).size) :
    ∃ i : Fin updated.size,
      (retainedSource source updated)[j].2 = updated[i] := by
  have hmem : (retainedSource source updated)[j] ∈
      (retainedSource source updated).toList :=
    Array.getElem_mem_toList j.isLt
  unfold retainedSource at hmem
  obtain ⟨i, hi, hmap⟩ := List.mem_filterMap.mp hmem
  have hiupdated : i < updated.size := by
    change i ∈ (List.range updated.size).filter
      (fun i => decide (0 < updated[i]?.getD 0)) at hi
    exact List.mem_range.mp (List.mem_filter.mp hi).1
  cases hs : source[i]? with
  | none => simp [hs] at hmap
  | some e =>
      simp [hs] at hmap
      have he : (retainedSource source updated)[j].2 =
          updated[i]?.getD 0 := by
        exact congrArg Prod.snd hmap.symm
      refine ⟨⟨i, hiupdated⟩, ?_⟩
      simpa [hiupdated] using he

/-- Restricting to positive indexed entries preserves any already proved
common denominator without increasing it. -/
noncomputable def retainedSource_commonDenominator {α : Type*}
    (source : Array (α × ℚ)) (updated : Array ℚ)
    (enc : CommonDenominator
      (fun i : Fin updated.size => updated[i])) :
    CommonDenominator
      (fun j : Fin (retainedSource source updated).size =>
        (retainedSource source updated)[j].2) := by
  classical
  let pick (j : Fin (retainedSource source updated).size) : Fin updated.size :=
    Classical.choose (retainedSource_weight_from_updated source updated j)
  refine
    { denominator := enc.denominator
      positive := enc.positive
      numerator := fun j => enc.numerator (pick j)
      represents := ?_ }
  intro j
  have hp := Classical.choose_spec
    (retainedSource_weight_from_updated source updated j)
  rw [hp]
  exact enc.represents (pick j)

#print axioms retainedSource_weight_from_updated
#print axioms retainedSource_commonDenominator

end CurrentAdditive.RationalCandidateCompletion
