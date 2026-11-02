import CurrentAdditive.TrialDivisorTest
import CurrentAdditive.TrialLoopCount

/-!
Sum of the *proved physical inner-loop* clocks over the frozen full trial
schedule. `fullTrialSchedule` is an upper envelope: `find?` and `all` may
short-circuit. This arithmetic is not itself a whole-program machine proof;
the outer controller and input preparation are separate obligations.
-/

namespace CurrentAdditive.FieldMachineHelper.TrialScheduleCost

open CurrentAdditive.FieldMachineHelper.TrialDividerTotal
open CurrentAdditive.FiniteFieldConstructor.TrialSearch
open CurrentAdditive.FiniteFieldMachine.RuntimeArithmetic

def pairClock (d e : Nat) : Nat :=
  divisionClock e (d - e + 1) + 1 + (e + 1)

def fullScheduleClock (d : Nat) : Nat :=
  ((fullTrialSchedule d).map fun p => pairClock d p.2.1).sum

def uniformPairBudget (d : Nat) : Nat :=
  (d + 1) * (4 * (d + 1) + 6) + d + 2

theorem scheduled_degree_le (d : Nat) (p : Nat × Nat × Nat)
    (hp : p ∈ fullTrialSchedule d) : p.2.1 ≤ d := by
  unfold fullTrialSchedule at hp
  obtain ⟨candidate, _, hinner⟩ := List.mem_flatMap.mp hp
  obtain ⟨e0, he0, hmap⟩ := List.mem_flatMap.mp hinner
  obtain ⟨tail, _, hpair⟩ := List.mem_map.mp hmap
  subst p
  have he : e0 < d / 2 := List.mem_range.mp he0
  simp
  omega

theorem pairClock_le (d e : Nat) (he : e ≤ d) :
    pairClock d e ≤ uniformPairBudget d := by
  have hdiv := divisionClock_remainder_le d e he
  unfold pairClock uniformPairBudget
  omega

theorem fullScheduleClock_le (d : Nat) :
    fullScheduleClock d ≤ pairCount d * uniformPairBudget d := by
  have hsum (l : List (Nat × Nat × Nat))
      (h : ∀ p ∈ l, p.2.1 ≤ d) :
      ((l.map fun p => pairClock d p.2.1).sum) ≤
        l.length * uniformPairBudget d := by
    induction l with
    | nil => simp
    | cons p rest ih =>
      have hp : p.2.1 ≤ d := h p (by simp)
      have hr : ∀ q ∈ rest, q.2.1 ≤ d := by
        intro q hq
        exact h q (by simp [hq])
      have htail := ih hr
      have hhead := pairClock_le d p.2.1 hp
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      omega
  simpa [fullScheduleClock, fullTrialSchedule_length] using
    hsum (fullTrialSchedule d) (scheduled_degree_le d)

theorem uniformPairBudget_quadratic (d : Nat) :
    uniformPairBudget d ≤ 12 * (d + 1) ^ 2 := by
  unfold uniformPairBudget
  nlinarith [sq_nonneg (d : ℤ)]

/-- Arithmetic sum of physical per-pair work has the requested R^(3/2) form. -/
theorem fullScheduleClock_lt_three_halves (d : Nat) :
    fullScheduleClock d <
      24 * 2 ^ d * 2 ^ (d / 2) * (d + 1) ^ 2 := by
  have hcount := pairCount_lt_three_halves_envelope d
  have hbudget := uniformPairBudget_quadratic d
  have hpositive : 0 < 12 * (d + 1) ^ 2 := by positivity
  calc
    fullScheduleClock d ≤ pairCount d * uniformPairBudget d :=
      fullScheduleClock_le d
    _ ≤ pairCount d * (12 * (d + 1) ^ 2) :=
      Nat.mul_le_mul_left _ hbudget
    _ < (2 * 2 ^ d * 2 ^ (d / 2)) * (12 * (d + 1) ^ 2) :=
      Nat.mul_lt_mul_of_pos_right hcount hpositive
    _ = 24 * 2 ^ d * 2 ^ (d / 2) * (d + 1) ^ 2 := by ring

#print axioms fullScheduleClock_lt_three_halves

end CurrentAdditive.FieldMachineHelper.TrialScheduleCost
