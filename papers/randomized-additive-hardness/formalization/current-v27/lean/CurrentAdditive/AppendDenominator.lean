import CurrentAdditive.CompressionDenominator

set_option maxHeartbeats 1000000

namespace CurrentAdditive.RationalCandidateCompletion

open CurrentAdditive.SequentialCode
open CurrentAdditive.RationalBitBounds

theorem appendSource_weight_from_factors {Y : Type*} {q : Nat}
    (source : Array ((Fin q → Y) × ℚ))
    (alphabet : Array (Y × ℚ))
    (j : Fin (appendSource source alphabet).size) :
    ∃ (i : Fin source.size) (t : Fin alphabet.size),
      (appendSource source alphabet)[j].2 = source[i].2 * alphabet[t].2 := by
  have hfold (l : List ((Fin q → Y) × ℚ))
      (hl : ∀ x ∈ l, x ∈ source.toList)
      (acc : Array ((Fin (q + 1) → Y) × ℚ))
      (hacc : ∀ e ∈ acc.toList,
        ∃ x ∈ source.toList, ∃ y ∈ alphabet.toList,
          e.2 = x.2 * y.2) :
      ∀ e ∈ (l.foldl (fun out x =>
        out ++ alphabet.map (fun y =>
          (appendWord x.1 y.1, x.2 * y.2))) acc).toList,
        ∃ x ∈ source.toList, ∃ y ∈ alphabet.toList,
          e.2 = x.2 * y.2 := by
    induction l generalizing acc with
    | nil => simpa using hacc
    | cons x xs ih =>
        have hx : x ∈ source.toList := hl x (by simp)
        have hxs : ∀ y ∈ xs, y ∈ source.toList := by
          intro y hy
          exact hl y (by simp [hy])
        have hnew : ∀ e ∈ (acc ++ alphabet.map (fun y =>
            (appendWord x.1 y.1, x.2 * y.2))).toList,
            ∃ x' ∈ source.toList, ∃ y ∈ alphabet.toList,
              e.2 = x'.2 * y.2 := by
          intro e he
          have he' : e ∈ acc.toList ∨
              e ∈ (alphabet.map (fun y =>
                (appendWord x.1 y.1, x.2 * y.2))).toList := by
            simpa using he
          rcases he' with ha | hb
          · exact hacc e ha
          · have hb' : e ∈ alphabet.toList.map (fun y =>
                (appendWord x.1 y.1, x.2 * y.2)) := by
              simpa only [Array.toList_map] using hb
            obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hb'
            refine ⟨x, hx, y, hy, ?_⟩
            exact congrArg Prod.snd hxy.symm
        simpa [List.foldl_cons] using ih hxs _ hnew
  have hresult : ∀ e ∈ (appendSource source alphabet).toList,
      ∃ x ∈ source.toList, ∃ y ∈ alphabet.toList,
        e.2 = x.2 * y.2 := by
    unfold appendSource
    rw [← Array.foldl_toList]
    exact hfold source.toList (by intro x hx; exact hx) #[]
      (by intro e he; simp at he)
  have hmem : (appendSource source alphabet)[j] ∈
      (appendSource source alphabet).toList :=
    Array.getElem_mem_toList j.isLt
  obtain ⟨x, hx, y, hy, hweight⟩ :=
    hresult _ hmem
  obtain ⟨i, hi, hix⟩ := Array.mem_iff_getElem.mp (by simpa using hx)
  obtain ⟨t, ht, hty⟩ := Array.mem_iff_getElem.mp (by simpa using hy)
  refine ⟨⟨i, hi⟩, ⟨t, ht⟩, ?_⟩
  simpa [hix, hty] using hweight

/-- The literal coordinate append multiplies the input-law denominator once,
independently of the number of resulting indexed words. -/
noncomputable def appendSource_commonDenominator {Y : Type*} {q : Nat}
    (source : Array ((Fin q → Y) × ℚ))
    (alphabet : Array (Y × ℚ))
    (es : CommonDenominator (fun i : Fin source.size => source[i].2))
    (ea : CommonDenominator (fun j : Fin alphabet.size => alphabet[j].2)) :
    CommonDenominator
      (fun t : Fin (appendSource source alphabet).size =>
        (appendSource source alphabet)[t].2) := by
  classical
  let pairs (t : Fin (appendSource source alphabet).size) :=
    Classical.choose (appendSource_weight_from_factors source alphabet t)
  let ia (t : Fin (appendSource source alphabet).size) :=
    Classical.choose (Classical.choose_spec
      (appendSource_weight_from_factors source alphabet t))
  let both := append_commonDenominator es ea
  refine
    { denominator := both.denominator
      positive := both.positive
      numerator := fun t => both.numerator (pairs t, ia t)
      represents := ?_ }
  intro t
  have hp := Classical.choose_spec
    (Classical.choose_spec
      (appendSource_weight_from_factors source alphabet t))
  rw [hp]
  exact both.represents (pairs t, ia t)

#print axioms appendSource_weight_from_factors
#print axioms appendSource_commonDenominator

end CurrentAdditive.RationalCandidateCompletion
