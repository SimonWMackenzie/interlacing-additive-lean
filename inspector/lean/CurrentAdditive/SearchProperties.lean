import CurrentAdditive.TrialSearch

namespace CurrentAdditive.FiniteFieldConstructor.TrialSearch

theorem firstPassing_passes {d modulus : ℕ}
    (h : firstPassing d = some modulus) :
    trialIrreducible d (modulus - 2 ^ d) = true := by
  have hh := List.find?_some (by simpa only [firstPassing] using h)
  exact hh

theorem firstPassing_is_candidate {d modulus : ℕ}
    (h : firstPassing d = some modulus) :
    ∃ tail < 2 ^ d, modulus = monicBits d tail := by
  have hm := List.mem_of_find?_eq_some (by simpa only [firstPassing] using h)
  simp only [List.mem_map, List.mem_range] at hm
  obtain ⟨tail, ht, heq⟩ := hm
  exact ⟨tail, ht, heq.symm⟩

theorem makeList_length {d n : ℕ} {output : List (ℕ × ℕ × List Bool)}
    (h : makeList d n = some output) :
    output.length = (2 ^ d) ^ 2 := by
  unfold makeList at h
  cases hf : firstPassing d with
  | none => simp [hf] at h
  | some modulus =>
      simp only [hf, Option.map_some, Option.some.injEq] at h
      subst output
      exact CurrentAdditive.FiniteFieldConstructor.StreamingPrinter.labelledWords_length
        d modulus n

#print axioms firstPassing_passes
#print axioms firstPassing_is_candidate
#print axioms makeList_length

end CurrentAdditive.FiniteFieldConstructor.TrialSearch
