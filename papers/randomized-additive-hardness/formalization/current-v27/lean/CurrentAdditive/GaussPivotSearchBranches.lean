import CurrentAdditive.GaussPivotSearchSemantic

/-! Branch forms of the exact physical first-hit/pivotTyped bridge. -/

namespace CurrentAdditive.GaussPivotSearchBranches

theorem selected_none_iff {m k : Nat}
    (B : Fin m → Fin k → ℚ) (j : Fin k) (r : Nat) :
    GaussFlagSearch.selected (GaussPivotSearchSemantic.flags B j) r = none ↔
      CurrentAdditive.SequentialTotality.pivotTyped B r j = none := by
  have h := GaussPivotSearchSemantic.selected_pivot_val B j r
  cases hp : CurrentAdditive.SequentialTotality.pivotTyped B r j with
  | none => rw [← h]; simp [hp]
  | some p => rw [← h]; simp [hp]

theorem selected_some_iff {m k : Nat}
    (B : Fin m → Fin k → ℚ) (j : Fin k) (r n : Nat) :
    GaussFlagSearch.selected (GaussPivotSearchSemantic.flags B j) r = some n ↔
      ∃ p : Fin m,
        CurrentAdditive.SequentialTotality.pivotTyped B r j = some p ∧
          p.val = n := by
  have h := GaussPivotSearchSemantic.selected_pivot_val B j r
  cases hp : CurrentAdditive.SequentialTotality.pivotTyped B r j with
  | none => rw [← h]; simp [hp]
  | some p =>
      rw [← h]
      simp [hp]

theorem found_false_iff {m k : Nat}
    (B : Fin m → Fin k → ℚ) (j : Fin k) (r : Nat) :
    (GaussFlagSearch.firstHit (GaussPivotSearchSemantic.flags B j) r).1 = false ↔
      CurrentAdditive.SequentialTotality.pivotTyped B r j = none := by
  rw [← selected_none_iff]
  unfold GaussFlagSearch.selected
  cases h : GaussFlagSearch.firstHit (GaussPivotSearchSemantic.flags B j) r with
  | mk flag n => cases flag <;> simp [h]

theorem found_true_row {m k : Nat}
    (B : Fin m → Fin k → ℚ) (j : Fin k) (r : Nat)
    (hfound : (GaussFlagSearch.firstHit
      (GaussPivotSearchSemantic.flags B j) r).1 = true) :
    ∃ p : Fin m,
      CurrentAdditive.SequentialTotality.pivotTyped B r j = some p ∧
      (GaussFlagSearch.firstHit
        (GaussPivotSearchSemantic.flags B j) r).2 = p.val := by
  have hsome : GaussFlagSearch.selected
      (GaussPivotSearchSemantic.flags B j) r =
      some (GaussFlagSearch.firstHit
        (GaussPivotSearchSemantic.flags B j) r).2 := by
    simp [GaussFlagSearch.selected, hfound]
  obtain ⟨p,hp,hval⟩ := (selected_some_iff B j r _).mp hsome
  exact ⟨p,hp,hval.symm⟩

#print axioms selected_none_iff
#print axioms selected_some_iff
#print axioms found_false_iff
#print axioms found_true_row

end CurrentAdditive.GaussPivotSearchBranches
