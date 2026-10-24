import CurrentAdditive.TrialSearchFirstCandidate

/-! Candidate-level iteration of the literal combined TM2 machine. -/

namespace CurrentAdditive.FieldSearchCompletion

set_option maxHeartbeats 1000000

open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedSearchState

theorem rejected_candidate_prefix (d c : Nat) (hd : 2 ≤ d)
    (hc : c < 2 ^ d)
    (hfail : ∀ x < c, CurrentAdditive.FiniteFieldConstructor.TrialSearch.trialIrreducible d x = false)
    (base : Registers) :
    ∃ steps ≤ c * prefixBudget d (d / 2),
      let g := run steps
        ⟨some (.outer .test), base, searchBank d 0 1 0⟩
      g.l = some (.outer .test) ∧
      g.stk = searchBank d c 1 0 := by
  induction c generalizing base with
  | zero =>
    refine ⟨0, by simp, ?_⟩
    exact ⟨rfl, rfl⟩
  | succ c ih =>
    have hc' : c < 2 ^ d := by omega
    have hprior : ∀ x < c,
        CurrentAdditive.FiniteFieldConstructor.TrialSearch.trialIrreducible d x = false := by
      intro x hx
      exact hfail x (by omega)
    obtain ⟨u, hu, hrun⟩ := ih hc' hprior base
    let g := run u ⟨some (.outer .test), base, searchBank d 0 1 0⟩
    change g.l = _ ∧ _ at hrun
    rcases hrun with ⟨hl, hs⟩
    obtain ⟨v, hv, hout⟩ := candidate_fails_to_next d c hd hc
      (hfail c (by omega)) g.var
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
      change (run v g).l = some (.outer .test) ∧
        (run v g).stk = searchBank d (c + 1) 1 0
      rw [hcfg]
      exact hout

#print axioms rejected_candidate_prefix

end CurrentAdditive.FieldSearchCompletion
