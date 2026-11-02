import CurrentAdditive.TrialSearch
import CurrentAdditive.RuntimeArithmetic

namespace CurrentAdditive.FiniteFieldConstructor.TrialSearch

open CurrentAdditive.FiniteFieldMachine.RuntimeArithmetic

def divisorSchedule (d : ℕ) : List (ℕ × ℕ) :=
  (List.range (d / 2)).flatMap fun e0 =>
    (List.range (2 ^ (e0 + 1))).map fun divisorTail =>
      (e0 + 1, divisorTail)

/-- The schedule is definitionally the same positive-degree nested test
performed by the executable predicate, including its empty `d=1` case. -/
theorem trialIrreducible_eq_schedule (d tail : ℕ) :
    trialIrreducible d tail =
      (divisorSchedule d).all fun e_divisorTail =>
        remainder d e_divisorTail.1
          (monicBits e_divisorTail.1 e_divisorTail.2)
          (monicBits d tail) != 0 := by
  simp only [divisorSchedule, List.all_flatMap, List.all_map]
  rfl

theorem firstPassing_eq_schedule (d : ℕ) :
    firstPassing d =
      ((List.range (2 ^ d)).map (monicBits d)).find?
        (fun candidate =>
          (divisorSchedule d).all fun e_divisorTail =>
            remainder d e_divisorTail.1
              (monicBits e_divisorTail.1 e_divisorTail.2)
              (monicBits d (candidate - 2 ^ d)) != 0) := by
  simp only [firstPassing]
  congr 1
  funext candidate
  exact trialIrreducible_eq_schedule d (candidate - 2 ^ d)

/-- The full potential test schedule of `firstPassing`: the first component
is the candidate tail, the second the positive divisor degree, and the
third the monic divisor tail. The executable `List.all` and `find?` may
stop early, so this is an upper envelope for their visits. -/
def fullTrialSchedule (d : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range (2 ^ d)).flatMap fun candidateTail =>
    (List.range (d / 2)).flatMap fun e0 =>
      (List.range (2 ^ (e0 + 1))).map fun divisorTail =>
        (candidateTail, e0 + 1, divisorTail)

theorem divisorSchedule_length (d : ℕ) :
    (divisorSchedule d).length = divisorCount (d / 2) := by
  have hsum (k : ℕ) :
      ((List.range k).map fun a => 2 ^ (a + 1)).sum =
        ∑ a ∈ Finset.range k, 2 ^ (a + 1) := by
    induction k with
    | zero => simp
    | succ k ih => simp [List.range_succ, Finset.sum_range_succ, ih]
  simpa [divisorSchedule, divisorCount, List.length_flatMap] using hsum (d / 2)

theorem divisorSchedule_one_empty : divisorSchedule 1 = [] := by
  simp [divisorSchedule]

theorem fullTrialSchedule_length (d : ℕ) :
    (fullTrialSchedule d).length = pairCount d := by
  have hsum (k : ℕ) :
      ((List.range k).map fun a => 2 ^ (a + 1)).sum =
        ∑ a ∈ Finset.range k, 2 ^ (a + 1) := by
    induction k with
    | zero => simp
    | succ k ih => simp [List.range_succ, Finset.sum_range_succ, ih]
  simpa [fullTrialSchedule, pairCount, divisorCount,
    List.length_flatMap] using hsum (d / 2)

theorem fullTrialSchedule_length_le_square (d : ℕ) (hd : 0 < d) :
    (fullTrialSchedule d).length ≤ (2 ^ d) ^ 2 := by
  rw [fullTrialSchedule_length]
  exact pairCount_le d hd

theorem fullTrialSchedule_one_empty : fullTrialSchedule 1 = [] := by
  simp [fullTrialSchedule]

#print axioms fullTrialSchedule_length
#print axioms fullTrialSchedule_length_le_square
#print axioms fullTrialSchedule_one_empty
#print axioms trialIrreducible_eq_schedule
#print axioms firstPassing_eq_schedule
#print axioms divisorSchedule_length
#print axioms divisorSchedule_one_empty

end CurrentAdditive.FiniteFieldConstructor.TrialSearch
