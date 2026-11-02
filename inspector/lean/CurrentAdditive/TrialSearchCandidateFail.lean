import CurrentAdditive.TrialSearchCandidatePass

/-! A rejected candidate physically resets the search to the next candidate.
The failing degree and divisor are selected from the exact executable
trial predicate, then every earlier test is traversed by the combined TM2. -/

namespace CurrentAdditive.FieldSearchCompletion

set_option maxHeartbeats 1000000

open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedSearchState
open CurrentAdditive.FieldMachineHelper.TrialSearchCorrectedEnvelope
open CurrentAdditive.FiniteFieldConstructor.TrialSearch

theorem prefixBudget_mono (d : Nat) : Monotone (prefixBudget d) := by
  intro j k hjk
  unfold prefixBudget
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hjk)

theorem candidate_fails_to_next (d c : Nat) (hd : 2 ≤ d)
    (hc : c + 1 < 2 ^ d) (hfail : trialIrreducible d c = false)
    (base : Registers) :
    ∃ steps ≤ prefixBudget d (d / 2),
      let g := run steps
        ⟨some (.outer .test), base, searchBank d c 1 0⟩
      g.l = some (.outer .test) ∧
      g.stk = searchBank d (c + 1) 1 0 := by
  have hex : ∃ i, i < d / 2 ∧ degreePass d c (i + 1) = false := by
    obtain ⟨i, hi, hn⟩ :=
      List.all_eq_false.mp (trialIrreducible_eq_degrees d c ▸ hfail)
    refine ⟨i, List.mem_range.mp hi, ?_⟩
    cases h : degreePass d c (i + 1) <;> simp_all
  let j := Nat.find hex
  have hj : j < d / 2 := (Nat.find_spec hex).1
  have hjfail : degreePass d c (j + 1) = false := (Nat.find_spec hex).2
  have hprior : ∀ i < j, degreePass d c (i + 1) = true := by
    intro i hi
    have hn : ¬(i < d / 2 ∧ degreePass d c (i + 1) = false) :=
      Nat.find_min hex hi
    have hi' : i < d / 2 := by omega
    cases h : degreePass d c (i + 1) <;> simp_all
  obtain ⟨u, hu, hprefix⟩ := passing_prefix d c (by omega)
    j hj hprior base
  let g := run u ⟨some (.outer .test), base, searchBank d c 1 0⟩
  change g.l = _ ∧ _ at hprefix
  rcases hprefix with ⟨hl, hs⟩
  obtain ⟨f, hf, hfailf, hpassf⟩ :=
    degreePass_false_first d c (j + 1) hjfail
  have hpass : ∀ x, 0 ≤ x → x < f →
      (remainder d (j + 1) (monicBits (j + 1) x)
        (monicBits d c) != 0) = true := by
    intro x _ hx
    exact hpassf x hx
  obtain ⟨v, hv, hout⟩ :=
    failing_degree_to_next_candidate d c (j + 1) 0 f
      (by omega) (by omega) hc (by omega) hf hpass hfailf g.var
  refine ⟨u + v, ?_, ?_⟩
  · have hterm : (f - 0 + 1) * correctedPairEnvelope d (j + 1) ≤
        2 ^ (j + 1) * correctedPairEnvelope d (j + 1) := by
      apply Nat.mul_le_mul_right
      omega
    have hstep := prefixBudget_succ d j
    have hmon := prefixBudget_mono d (by omega : j + 1 ≤ d / 2)
    omega
  · rw [CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.run_add]
    have hcfg : g = ⟨some (.outer .test), g.var,
        searchBank d c (j + 1) 0⟩ := by
      change g.stk = _ at hs
      rcases g with ⟨l, r, S⟩
      change l = _ at hl
      cases hl
      change S = _ at hs
      cases hs
      rfl
    change (run v g).l = some (.outer .test) ∧
      (run v g).stk = searchBank d (c + 1) 1 0
    rw [hcfg]
    exact hout

#print axioms candidate_fails_to_next

end CurrentAdditive.FieldSearchCompletion
