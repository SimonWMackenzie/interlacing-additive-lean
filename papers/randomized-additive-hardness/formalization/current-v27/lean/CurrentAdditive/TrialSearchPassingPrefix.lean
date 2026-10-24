import CurrentAdditive.TrialSearchDegreeLogic

/-! Physical execution through an initial sequence of passing divisor degrees. -/

namespace CurrentAdditive.FieldSearchCompletion

set_option maxHeartbeats 1000000

open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedSearchState
open CurrentAdditive.FieldMachineHelper.TrialSearchCorrectedEnvelope

def prefixBudget (d j : Nat) : Nat :=
  ∑ i ∈ Finset.range j, 2 ^ (i + 1) * correctedPairEnvelope d (i + 1)

theorem prefixBudget_succ (d j : Nat) :
    prefixBudget d (j + 1) =
      prefixBudget d j + 2 ^ (j + 1) * correctedPairEnvelope d (j + 1) := by
  simp [prefixBudget, Finset.sum_range_succ]

theorem passing_prefix (d c : Nat) (hc : c < 2 ^ d) :
    ∀ j, j < d / 2 →
      (∀ i < j, degreePass d c (i + 1) = true) →
      ∀ base : Registers,
        ∃ steps ≤ prefixBudget d j,
          let g := run steps
            ⟨some (.outer .test), base, searchBank d c 1 0⟩
          g.l = some (.outer .test) ∧
          g.stk = searchBank d c (j + 1) 0 := by
  intro j
  induction j with
  | zero =>
    intro _ _ base
    refine ⟨0, by simp [prefixBudget], ?_⟩
    exact ⟨rfl, rfl⟩
  | succ j ih =>
    intro hj hall base
    have hj' : j < d / 2 := by omega
    have hprior : ∀ i < j, degreePass d c (i + 1) = true := by
      intro i hi
      exact hall i (by omega)
    obtain ⟨u, hu, hrun⟩ := ih hj' hprior base
    let g := run u ⟨some (.outer .test), base, searchBank d c 1 0⟩
    change g.l = _ ∧ _ at hrun
    rcases hrun with ⟨hl, hs⟩
    have he : 0 < j + 1 := by omega
    have he' : j + 1 < d / 2 := by omega
    have hpass : ∀ x, 0 ≤ x → x < 2 ^ (j + 1) →
        (CurrentAdditive.FiniteFieldConstructor.TrialSearch.remainder d (j + 1)
          (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits (j + 1) x)
          (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d c) != 0) = true := by
      intro x _ hx
      exact degreePass_true d c (j + 1) (hall j (by omega)) x hx
    obtain ⟨v, hv, hout⟩ :=
      passing_degree_to_next d c (j + 1) 0 (2 ^ (j + 1))
        he he' hc (by omega) (by positivity) hpass g.var
    refine ⟨u + v, ?_, ?_⟩
    · rw [prefixBudget_succ]
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
        (run v g).stk = searchBank d c (j + 1 + 1) 0
      rw [hcfg]
      exact hout

#print axioms passing_prefix

end CurrentAdditive.FieldSearchCompletion
