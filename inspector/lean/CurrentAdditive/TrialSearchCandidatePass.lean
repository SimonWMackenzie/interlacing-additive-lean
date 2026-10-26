import CurrentAdditive.TrialSearchPassingPrefix

/-! A passing candidate reaches the literal success state of the combined
physical search machine. -/

namespace CurrentAdditive.FieldSearchCompletion

set_option maxHeartbeats 1000000

open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedSearchState
open CurrentAdditive.FieldMachineHelper.TrialSearchCorrectedEnvelope
open CurrentAdditive.FiniteFieldConstructor.TrialSearch
open CurrentAdditive.FieldMachineHelper.TrialCounterMachine (counterWord)

theorem candidate_passes (d c : Nat) (hd : 2 ≤ d)
    (hc : c < 2 ^ d) (hpass : trialIrreducible d c = true)
    (base : Registers) :
    ∃ steps ≤ prefixBudget d (d / 2),
      let g := run steps
        ⟨some (.outer .test), base, searchBank d c 1 0⟩
      g.l = some (.outer .success) ∧
      g.stk 0 = counterWord d c := by
  have hhalf : 0 < d / 2 := Nat.div_pos hd (by omega)
  let j := d / 2 - 1
  have hj : j < d / 2 := by omega
  have hall : ∀ i < d / 2, degreePass d c (i + 1) = true := by
    intro i hi
    have h := (List.all_eq_true.mp (trialIrreducible_eq_degrees d c ▸ hpass))
      i (List.mem_range.mpr hi)
    exact h
  obtain ⟨u, hu, hprefix⟩ :=
    passing_prefix d c hc j hj (by
      intro i hi
      exact hall i (by omega)) base
  let g := run u ⟨some (.outer .test), base, searchBank d c 1 0⟩
  change g.l = _ ∧ _ at hprefix
  rcases hprefix with ⟨hl, hs⟩
  have heq : j + 1 = d / 2 := by omega
  have hpair : ∀ x, 0 ≤ x → x < 2 ^ (j + 1) →
      (remainder d (j + 1) (monicBits (j + 1) x)
        (monicBits d c) != 0) = true := by
    intro x _ hx
    exact degreePass_true d c (j + 1)
      (hall j hj) x hx
  obtain ⟨v, hv, hout⟩ :=
    passing_final_degree d c (j + 1) 0 (2 ^ (j + 1))
      (by omega) heq hc (by omega) (by positivity) hpair g.var
  refine ⟨u + v, ?_, ?_⟩
  · have hbudget := prefixBudget_succ d j
    have hindex : j + 1 = d / 2 := by omega
    rw [← hindex, hbudget]
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
    change (run v g).l = some (.outer .success) ∧
      (run v g).stk 0 = counterWord d c
    rw [hcfg]
    exact hout

#print axioms candidate_passes

end CurrentAdditive.FieldSearchCompletion
