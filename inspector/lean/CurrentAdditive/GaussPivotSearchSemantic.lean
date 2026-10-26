import CurrentAdditive.GaussAdaptedPrefixIndex
import CurrentAdditive.GaussFlagSearch

set_option maxHeartbeats 1000000

/-! The physical Boolean flag selector chooses the same first row as
`SequentialTotality.pivotTyped`. -/

namespace CurrentAdditive.GaussPivotSearchSemantic

def flags {m k : Nat} (B : Fin m → Fin k → ℚ) (j : Fin k) : List Bool :=
  (List.finRange m).map (fun i => decide (B i j ≠ 0))

private theorem selected_true (xs : List Bool) :
    GaussFlagSearch.selected (true :: xs) 0 = some 0 := rfl

private theorem selected_false (xs : List Bool) :
    GaussFlagSearch.selected (false :: xs) 0 =
      (GaussFlagSearch.selected xs 0).map Nat.succ := by
  change (if (GaussFlagSearch.firstHit xs 0).1 then
      some ((GaussFlagSearch.firstHit xs 0).2+1) else none) =
    (if (GaussFlagSearch.firstHit xs 0).1 then
      some (GaussFlagSearch.firstHit xs 0).2 else none).map Nat.succ
  cases h : GaussFlagSearch.firstHit xs 0 with
  | mk found n =>
      cases found <;> rfl

private theorem selected_succ (b : Bool) (xs : List Bool) (r : Nat) :
    GaussFlagSearch.selected (b :: xs) (r+1) =
      (GaussFlagSearch.selected xs r).map Nat.succ := by
  change (if (GaussFlagSearch.firstHit xs r).1 then
      some ((GaussFlagSearch.firstHit xs r).2+1) else none) =
    (if (GaussFlagSearch.firstHit xs r).1 then
      some (GaussFlagSearch.firstHit xs r).2 else none).map Nat.succ
  cases h : GaussFlagSearch.firstHit xs r with
  | mk found n =>
      cases found <;> rfl

theorem selected_pivot_val {m k : Nat}
    (B : Fin m → Fin k → ℚ) (j : Fin k) (r : Nat) :
    (CurrentAdditive.SequentialTotality.pivotTyped B r j).map Fin.val =
      CurrentAdditive.GaussFlagSearch.selected (flags B j) r := by
  induction m generalizing r with
  | zero =>
      simp [CurrentAdditive.SequentialTotality.pivotTyped,
        CurrentAdditive.GaussFlagSearch.selected,
        CurrentAdditive.GaussFlagSearch.firstHit, flags]
  | succ m ih =>
      let tail : Fin m → Fin k → ℚ := fun i j => B i.succ j
      cases r with
      | zero =>
          by_cases hz : B 0 j ≠ 0
          · simp [CurrentAdditive.SequentialTotality.pivotTyped,
              List.finRange_succ, flags, hz, selected_true]
          · have htail := ih tail 0
            have hleft :
                (CurrentAdditive.SequentialTotality.pivotTyped B 0 j).map Fin.val =
                (CurrentAdditive.SequentialTotality.pivotTyped tail 0 j).map
                  (fun x => x.val+1) := by
              simp [CurrentAdditive.SequentialTotality.pivotTyped,
                List.finRange_succ, List.find?_map, hz, tail,
                Function.comp_def]
            have hflags : flags B j = false :: flags tail j := by
              have hz0 : B 0 j = 0 := by
                by_contra h
                exact hz h
              simp [flags, List.finRange_succ, tail, hz0]
            rw [hleft, hflags, selected_false]
            simpa [Option.map_map, Function.comp_def] using
              congrArg (Option.map Nat.succ) htail
      | succ r =>
          have htail := ih tail r
          have hleft :
              (CurrentAdditive.SequentialTotality.pivotTyped B (r+1) j).map Fin.val =
              (CurrentAdditive.SequentialTotality.pivotTyped tail r j).map
                (fun x => x.val+1) := by
            simp [CurrentAdditive.SequentialTotality.pivotTyped,
              List.finRange_succ, List.find?_map, tail,
              Function.comp_def]
          have hflags : flags B j = decide (B 0 j ≠ 0) :: flags tail j := by
            simp [flags, List.finRange_succ, tail]
          rw [hleft, hflags, selected_succ]
          simpa [Option.map_map, Function.comp_def] using
            congrArg (Option.map Nat.succ) htail

#print axioms selected_pivot_val

end CurrentAdditive.GaussPivotSearchSemantic
