import CurrentAdditive.TrialIrreducibleCorrect
import CurrentAdditive.SearchProperties
import CurrentAdditive.IrreducibleExistence

namespace CurrentAdditive.FiniteFieldConstructor

open BitPolynomialBridge

private theorem find?_exists_of_mem_true {α : Type*} (xs : List α)
    (p : α → Bool) (a : α) (ha : a ∈ xs) (hp : p a = true) :
    ∃ b, xs.find? p = some b := by
  induction xs with
  | nil => cases ha
  | cons x xs ih =>
      cases hpx : p x with
      | true => exact ⟨x, by simp [List.find?, hpx]⟩
      | false =>
          rcases List.mem_cons.mp ha with rfl | htail
          · simp [hpx] at hp
          · obtain ⟨b, hb⟩ := ih htail
            exact ⟨b, by simp [List.find?, hpx, hb]⟩

namespace TrialSearch

theorem firstPassing_total (d : ℕ) (hd : 0 < d) :
    ∃ modulus, firstPassing d = some modulus := by
  obtain ⟨f, hfmonic, hfirr, hfdeg⟩ := exists_binary_irreducible d hd
  obtain ⟨tail, htail, hpoly⟩ := exists_monicBits d f hfmonic hfdeg
  have hpass : trialIrreducible d tail = true :=
    (trial_irreducible_iff d tail hd htail).mpr (hpoly ▸ hfirr)
  have hmem : monicBits d tail ∈ (List.range (2 ^ d)).map (monicBits d) := by
    simp only [List.mem_map, List.mem_range]
    exact ⟨tail, htail, rfl⟩
  have htarget :
      (fun candidate => trialIrreducible d (candidate - 2 ^ d))
        (monicBits d tail) = true := by
    simpa only [monicBits, Nat.add_sub_cancel_left] using hpass
  exact find?_exists_of_mem_true _ _ _ hmem htarget

theorem firstPassing_correct {d modulus : ℕ} (hd : 0 < d)
    (h : firstPassing d = some modulus) :
    Irreducible (polynomial (d + 1) modulus) := by
  obtain ⟨tail, htail, hmodulus⟩ := firstPassing_is_candidate h
  subst modulus
  have hpass : trialIrreducible d tail = true := by
    simpa only [monicBits, Nat.add_sub_cancel_left] using firstPassing_passes h
  exact (trial_irreducible_iff d tail hd htail).mp hpass

theorem makeList_total (d n : ℕ) (hd : 0 < d) :
    ∃ output, makeList d n = some output := by
  obtain ⟨modulus, hmodulus⟩ := firstPassing_total d hd
  exact ⟨StreamingPrinter.labelledWords d modulus n, by simp [makeList, hmodulus]⟩

#print axioms firstPassing_total
#print axioms firstPassing_correct
#print axioms makeList_total

end TrialSearch
end CurrentAdditive.FiniteFieldConstructor
