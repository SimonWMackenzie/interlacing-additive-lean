import CurrentAdditive.SequentialCode

namespace CurrentAdditive.RationalBitBounds

open CurrentAdditive.SequentialCode

private def ratioStep (weights coeff : Array ℚ) (best : Option ℚ) (i : Nat) : Option ℚ :=
  let ai := coeff[i]?.getD 0
  if 0 < ai then
    let ratio := (weights[i]?.getD 0) / ai
    match best with
    | none => some ratio
    | some previous => some (min previous ratio)
  else best

private def partialMinimumRatio (weights coeff : Array ℚ) (n : Nat) : Option ℚ :=
  (List.range n).foldl (ratioStep weights coeff) none

/-- Every successful finite minimum is one of the ratios physically scanned
by the code; in particular no unattained rational value is synthesized. -/
theorem partialMinimumRatio_attained (weights coeff : Array ℚ) (n : Nat) (t : ℚ)
    (h : partialMinimumRatio weights coeff n = some t) :
    ∃ j ∈ List.range n,
      0 < (coeff[j]?.getD 0) ∧
      t = (weights[j]?.getD 0) / (coeff[j]?.getD 0) := by
  induction n generalizing t with
  | zero => simp [partialMinimumRatio] at h
  | succ n ih =>
      have hstep : partialMinimumRatio weights coeff (n + 1) =
          ratioStep weights coeff (partialMinimumRatio weights coeff n) n := by
        simp [partialMinimumRatio, List.range_succ, List.foldl_append]
      rw [hstep] at h
      by_cases ha : 0 < (coeff[n]?.getD 0)
      · cases hp : partialMinimumRatio weights coeff n with
        | none =>
            simp [ratioStep, ha, hp] at h
            cases h
            exact ⟨n, by simp, ha, rfl⟩
        | some previous =>
            simp [ratioStep, ha, hp] at h
            cases h
            rcases le_total previous
              ((weights[n]?.getD 0) / (coeff[n]?.getD 0)) with hle | hle
            · rw [min_eq_left hle]
              obtain ⟨j, hj, hjpos, hjratio⟩ := ih previous hp
              exact ⟨j, List.mem_range.mpr (by have := List.mem_range.mp hj; omega),
                hjpos, hjratio⟩
            · rw [min_eq_right hle]
              exact ⟨n, by simp, ha, rfl⟩
      · have hprev : partialMinimumRatio weights coeff n = some t := by
          simpa [ratioStep, ha] using h
        obtain ⟨j, hj, hjpos, hjratio⟩ := ih t hprev
        exact ⟨j, List.mem_range.mpr (by have := List.mem_range.mp hj; omega),
          hjpos, hjratio⟩

theorem minimumRatio_attained (weights coeff : Array ℚ) (t : ℚ)
    (h : minimumRatio weights coeff = some t) :
    ∃ j ∈ List.range (min weights.size coeff.size),
      0 < (coeff[j]?.getD 0) ∧
      t = (weights[j]?.getD 0) / (coeff[j]?.getD 0) := by
  apply partialMinimumRatio_attained weights coeff _ t
  simpa [partialMinimumRatio, minimumRatio, ratioStep] using h

end CurrentAdditive.RationalBitBounds
