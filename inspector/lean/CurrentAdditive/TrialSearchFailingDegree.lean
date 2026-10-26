import CurrentAdditive.TrialSearchPassingDegree

/-! A first failing divisor physically advances the candidate counter. -/

namespace CurrentAdditive.FieldSearchCompletion

set_option maxHeartbeats 1000000

open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedSearchState
open CurrentAdditive.FieldMachineHelper.TrialSearchCorrectedEnvelope
open CurrentAdditive.FiniteFieldConstructor.TrialSearch (monicBits remainder)

theorem failing_degree_to_next_candidate
    (d c e t f : Nat) (he : 0 < e) (hed : e ≤ d / 2)
    (hc : c + 1 < 2 ^ d) (htf : t ≤ f) (hf : f < 2 ^ e)
    (hpass : ∀ u, t ≤ u → u < f →
      (remainder d e (monicBits e u) (monicBits d c) != 0) = true)
    (hfail : (remainder d e (monicBits e f) (monicBits d c) != 0) = false)
    (base : Registers) :
    ∃ steps ≤ (f - t + 1) * correctedPairEnvelope d e,
      let g := run steps
        ⟨some (.outer .test), base, searchBank d c e t⟩
      g.l = some (.outer .test) ∧
      g.stk = searchBank d (c + 1) 1 0 := by
  generalize hdist : f - t = n
  induction n using Nat.strong_induction_on generalizing t base with
  | h n ih =>
    by_cases hfirst : t = f
    · subst f
      obtain ⟨u, hu, hout⟩ :=
        fail_nonlast_candidate d c e t he hed hc hf hfail base
      refine ⟨u, ?_, hout⟩
      have hb := fail_nonlast_budget d e hed
      have hnzero : n = 0 := by omega
      rw [hnzero]
      simp only [Nat.zero_add, Nat.one_mul]
      omega
    · have hbefore : t < f := by omega
      have hnext : t + 1 < 2 ^ e := by omega
      have hed' : e ≤ d := by omega
      obtain ⟨u, hu, hrun⟩ :=
        combined_pass_nonlast_divisor d c e t hed' (by omega) hnext
          (hpass t (by omega) hbefore) base
      let g := run u ⟨some (.outer .test), base, searchBank d c e t⟩
      change g.l = _ ∧ _ at hrun
      rcases hrun with ⟨hl, hs⟩
      have hpass' : ∀ x, t + 1 ≤ x → x < f →
          (remainder d e (monicBits e x) (monicBits d c) != 0) = true := by
        intro x hx hx'
        exact hpass x (by omega) hx'
      obtain ⟨v, hv, hout⟩ :=
        ih (f - (t + 1)) (by omega) (t + 1) (by omega)
          hpass' g.var rfl
      refine ⟨u + v, ?_, ?_⟩
      · have hb := nonlast_divisor_budget d e hed'
        have hmul : (f - t + 1) * correctedPairEnvelope d e =
            (f - (t + 1) + 1) * correctedPairEnvelope d e +
              correctedPairEnvelope d e := by
          conv_lhs => rw [show f - t + 1 = (f - (t + 1) + 1) + 1 by omega]
          ring
        have hn : n = f - t := hdist.symm
        rw [hn]
        omega
      · rw [CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.run_add]
        have hcfg : g = ⟨some (.outer .test), g.var,
            searchBank d c e (t + 1)⟩ := by
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

#print axioms failing_degree_to_next_candidate

end CurrentAdditive.FieldSearchCompletion
