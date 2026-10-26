import CurrentAdditive.TrialSearchCandidateFail

/-! The frozen executable search selects a passing tail and rejects every
smaller tail; this is the semantic bridge for the physical candidate loop. -/

namespace CurrentAdditive.FieldSearchCompletion

open CurrentAdditive.FiniteFieldConstructor.TrialSearch

def tailFind (d : Nat) : Option Nat :=
  (List.range (2 ^ d)).find? (trialIrreducible d)

theorem firstPassing_eq_tailFind (d : Nat) :
    firstPassing d = (tailFind d).map (monicBits d) := by
  simp [firstPassing, tailFind, List.find?_map, Function.comp_def, monicBits]

theorem tailFind_first_properties {d c : Nat}
    (h : tailFind d = some c) :
    c < 2 ^ d ∧ trialIrreducible d c = true ∧
      ∀ u < c, trialIrreducible d u = false := by
  obtain ⟨hp, i, hi, hitem, hprior⟩ :=
    List.find?_eq_some_iff_getElem.mp h
  have hic : i = c := by
    simpa [List.getElem_range hi] using hitem
  subst i
  refine ⟨by simpa using hi, hp, ?_⟩
  intro u hu
  have hu' : u < (List.range (2 ^ d)).length := by omega
  have hnot := hprior u hu
  simp only [List.getElem_range hu'] at hnot
  cases hv : trialIrreducible d u <;> simp_all

theorem firstPassing_first_properties {d c : Nat}
    (h : firstPassing d = some (monicBits d c)) :
    c < 2 ^ d ∧ trialIrreducible d c = true ∧
      ∀ u < c, trialIrreducible d u = false := by
  rw [firstPassing_eq_tailFind] at h
  cases hf : tailFind d with
  | none => simp [hf] at h
  | some x =>
    have heq : x = c := by
      simp only [hf, Option.map_some, Option.some.injEq] at h
      simp only [monicBits] at h
      omega
    subst x
    exact tailFind_first_properties hf

#print axioms firstPassing_first_properties

end CurrentAdditive.FieldSearchCompletion
