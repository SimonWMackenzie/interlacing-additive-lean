import Mathlib.Data.Nat.Find

/-!
An all-input, fuel-bounded outer search for the first dyadic exponent whose
explicit Boolean test passes. The manuscript's cutoff gives the final fuel
bound once the exact rational/integer-power test is supplied. This module does
not treat an abstract Boolean callback as a physical bit machine.
-/

namespace CurrentAdditive.PublicScheduleBoundedSearch

def firstInRange (test : ℕ → Bool) : ℕ → ℕ → Option ℕ
  | start, 0 => if test start then some start else none
  | start, fuel + 1 =>
      if test start then some start else firstInRange test (start + 1) fuel

theorem firstInRange_sound (test : ℕ → Bool) (start fuel L : ℕ)
    (h : firstInRange test start fuel = some L) :
    start ≤ L ∧ L ≤ start + fuel ∧ test L = true ∧
      ∀ k, start ≤ k → k < L → test k = false := by
  induction fuel generalizing start with
  | zero =>
      by_cases ht : test start = true
      · simp [firstInRange, ht] at h
        subst L
        exact ⟨le_rfl, by omega, ht, by intros; omega⟩
      · have hf : test start = false := by cases hh : test start <;> simp_all
        simp [firstInRange, hf] at h
  | succ fuel ih =>
      by_cases ht : test start = true
      · simp [firstInRange, ht] at h
        subst L
        exact ⟨le_rfl, by omega, ht, by intros; omega⟩
      · have hf : test start = false := by cases hh : test start <;> simp_all
        have htail : firstInRange test (start + 1) fuel = some L := by
          simpa [firstInRange, hf] using h
        obtain ⟨hlo, hhi, hgood, hfirst⟩ := ih (start + 1) htail
        refine ⟨by omega, by omega, hgood, ?_⟩
        intro k hk hkL
        by_cases hks : k = start
        · simpa [hks] using hf
        · exact hfirst k (by omega) hkL

theorem firstInRange_complete (test : ℕ → Bool) (start fuel witness : ℕ)
    (hlo : start ≤ witness) (hhi : witness ≤ start + fuel)
    (hpass : test witness = true) :
    ∃ L, firstInRange test start fuel = some L := by
  induction fuel generalizing start with
  | zero =>
      have hw : witness = start := by omega
      exact ⟨start, by simpa [firstInRange, hw] using hpass⟩
  | succ fuel ih =>
      by_cases ht : test start = true
      · exact ⟨start, by simp [firstInRange, ht]⟩
      · have hf : test start = false := by cases hh : test start <;> simp_all
        have hnext : start + 1 ≤ witness := by
          have hne : witness ≠ start := by
            intro heq
            rw [heq] at hpass
            simp [hf] at hpass
          omega
        obtain ⟨L, hL⟩ := ih (start + 1) hnext (by omega)
        exact ⟨L, by simpa [firstInRange, hf] using hL⟩

/-- Starting from an explicit logarithmic floor, scan only up to the already
proved graph-independent cutoff. On arbitrary inputs, failure is an ordinary
`none` value; the function never uses a mathematical search oracle. -/
def firstPassingAtMost (test : ℕ → Bool) (start bound : ℕ) : Option ℕ :=
  firstInRange test start (bound - start)

theorem firstPassingAtMost_sound (test : ℕ → Bool) (start bound L : ℕ)
    (hbound : start ≤ bound)
    (h : firstPassingAtMost test start bound = some L) :
    start ≤ L ∧ L ≤ bound ∧ test L = true ∧
      ∀ k, start ≤ k → k < L → test k = false := by
  have hs := firstInRange_sound test start (bound - start) L h
  simpa only [firstPassingAtMost, Nat.add_sub_of_le hbound] using hs

theorem firstPassingAtMost_complete (test : ℕ → Bool) (start bound : ℕ)
    (hbound : start ≤ bound) (hpass : test bound = true) :
    ∃ L, firstPassingAtMost test start bound = some L := by
  exact firstInRange_complete test start (bound - start) bound hbound
    (by omega) hpass

/-- A total output convention for malformed inputs or a failed test. On
promised inputs, the last candidate passes and this fallback is never used. -/
def selectedLog (test : ℕ → Bool) (start bound : ℕ) : ℕ :=
  (firstPassingAtMost test start bound).getD bound

theorem selectedLog_spec (test : ℕ → Bool) (start bound : ℕ)
    (hbound : start ≤ bound) (hpass : test bound = true) :
    start ≤ selectedLog test start bound ∧
    selectedLog test start bound ≤ bound ∧
    test (selectedLog test start bound) = true ∧
    ∀ k, start ≤ k → k < selectedLog test start bound → test k = false := by
  obtain ⟨L, hL⟩ := firstPassingAtMost_complete test start bound hbound hpass
  have hs := firstPassingAtMost_sound test start bound L hbound hL
  simpa [selectedLog, hL] using hs

#print axioms firstInRange_sound
#print axioms firstInRange_complete
#print axioms firstPassingAtMost_sound
#print axioms firstPassingAtMost_complete
#print axioms selectedLog_spec

end CurrentAdditive.PublicScheduleBoundedSearch
