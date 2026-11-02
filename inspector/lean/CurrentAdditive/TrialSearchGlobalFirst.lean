import CurrentAdditive.TrialSearchCandidatePrefix

/-! Exact first-passing tail for one literal twelve-stack TM2 search run,
starting at the degree-derived search bank. -/

namespace CurrentAdditive.FieldSearchCompletion

set_option maxHeartbeats 1000000

open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedSearchState
open CurrentAdditive.FieldMachineHelper.TrialCounterMachine (counterWord)
open CurrentAdditive.FiniteFieldConstructor.TrialSearch

theorem run_firstPassing_from_test (d c : Nat) (hd : 2 ≤ d)
    (hfirst : firstPassing d = some (monicBits d c))
    (base : Registers) :
    ∃ steps ≤ (c + 1) * prefixBudget d (d / 2),
      let g := run steps
        ⟨some (.outer .test), base, searchBank d 0 1 0⟩
      g.l = some (.outer .success) ∧
      g.stk 0 = counterWord d c := by
  obtain ⟨hc, hpass, hprior⟩ := firstPassing_first_properties hfirst
  obtain ⟨u, hu, hprefix⟩ := rejected_candidate_prefix d c hd hc hprior base
  let g := run u ⟨some (.outer .test), base, searchBank d 0 1 0⟩
  change g.l = _ ∧ _ at hprefix
  rcases hprefix with ⟨hl, hs⟩
  obtain ⟨v, hv, hout⟩ := candidate_passes d c hd hc hpass g.var
  refine ⟨u + v, ?_, ?_⟩
  · simp only [Nat.succ_mul]
    omega
  · rw [CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.run_add]
    have hcfg : g = ⟨some (.outer .test), g.var,
        searchBank d c 1 0⟩ := by
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

#print axioms run_firstPassing_from_test

end CurrentAdditive.FieldSearchCompletion
