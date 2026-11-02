import CurrentAdditive.TrialSearchPairBudget

/-! A whole divisor degree physically executes in the combined twelve-stack
machine when every candidate divisor at that degree passes. -/

namespace CurrentAdditive.FieldSearchCompletion

set_option maxHeartbeats 1000000

open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedSearchState
open CurrentAdditive.FieldMachineHelper.TrialSearchCorrectedEnvelope
open CurrentAdditive.FiniteFieldConstructor.TrialSearch (monicBits remainder)

theorem passing_degree_to_next
    (d c e t k : Nat) (he : 0 < e) (helt : e < d / 2)
    (hc : c < 2 ^ d) (ht : t + k = 2 ^ e)
    (htail0 : t < 2 ^ e)
    (hpass : ∀ u, t ≤ u → u < 2 ^ e →
      (remainder d e (monicBits e u) (monicBits d c) != 0) = true)
    (base : Registers) :
    ∃ steps ≤ k * correctedPairEnvelope d e,
      let g := run steps
        ⟨some (.outer .test), base, searchBank d c e t⟩
      g.l = some (.outer .test) ∧
      g.stk = searchBank d c (e + 1) 0 := by
  induction k using Nat.strong_induction_on generalizing t base with
  | h k ih =>
    have hk : 0 < k := by omega
    by_cases hlast : k = 1
    · have htlast : t + 1 = 2 ^ e := by omega
      have htail : t < 2 ^ e := by omega
      obtain ⟨u, hu, hrun⟩ :=
        pass_last_divisor_next_degree d c e t he helt hc htlast
          (hpass t (by omega) htail) base
      refine ⟨u, ?_, hrun⟩
      have hb := last_divisor_budget d e helt
      rw [hlast]
      simp only [Nat.one_mul]
      omega
    · have hkgt : 1 < k := by omega
      have htail : t + 1 < 2 ^ e := by omega
      have hed : e ≤ d := by omega
      obtain ⟨u, hu, hrun⟩ :=
        combined_pass_nonlast_divisor d c e t hed hc htail
          (hpass t (by omega) (by omega)) base
      let g := run u ⟨some (.outer .test), base, searchBank d c e t⟩
      change g.l = _ ∧ _ at hrun
      rcases hrun with ⟨hl, hs⟩
      have hpass' : ∀ x, t + 1 ≤ x → x < 2 ^ e →
          (remainder d e (monicBits e x) (monicBits d c) != 0) = true := by
        intro x hx hx'
        exact hpass x (by omega) hx'
      obtain ⟨v, hv, hout⟩ :=
        ih (k - 1) (by omega) (t + 1) (by omega)
          (by omega) hpass' g.var
      refine ⟨u + v, ?_, ?_⟩
      · have hb := nonlast_divisor_budget d e hed
        have hmul : k * correctedPairEnvelope d e =
            (k - 1) * correctedPairEnvelope d e +
              correctedPairEnvelope d e := by
          conv_lhs => rw [show k = (k - 1) + 1 by omega]
          ring
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
          (run v g).stk = searchBank d c (e + 1) 0
        rw [hcfg]
        exact hout

#print axioms passing_degree_to_next

theorem passing_final_degree
    (d c e t k : Nat) (he : 0 < e) (heq : e = d / 2)
    (hc : c < 2 ^ d) (ht : t + k = 2 ^ e)
    (htail0 : t < 2 ^ e)
    (hpass : ∀ u, t ≤ u → u < 2 ^ e →
      (remainder d e (monicBits e u) (monicBits d c) != 0) = true)
    (base : Registers) :
    ∃ steps ≤ k * correctedPairEnvelope d e,
      let g := run steps
        ⟨some (.outer .test), base, searchBank d c e t⟩
      g.l = some (.outer .success) ∧
      g.stk 0 =
        CurrentAdditive.FieldMachineHelper.TrialCounterMachine.counterWord d c := by
  induction k using Nat.strong_induction_on generalizing t base with
  | h k ih =>
    have hk : 0 < k := by omega
    by_cases hlast : k = 1
    · have htlast : t + 1 = 2 ^ e := by omega
      have htail : t < 2 ^ e := by omega
      obtain ⟨u, hu, hrun⟩ :=
        pass_last_degree d c e t heq (by omega) hc htlast
          (hpass t (by omega) htail) base
      refine ⟨u, ?_, hrun⟩
      have hb := last_degree_budget d e heq he
      rw [hlast]
      simp only [Nat.one_mul]
      omega
    · have hkgt : 1 < k := by omega
      have htail : t + 1 < 2 ^ e := by omega
      have hed : e ≤ d := by omega
      obtain ⟨u, hu, hrun⟩ :=
        combined_pass_nonlast_divisor d c e t hed hc htail
          (hpass t (by omega) (by omega)) base
      let g := run u ⟨some (.outer .test), base, searchBank d c e t⟩
      change g.l = _ ∧ _ at hrun
      rcases hrun with ⟨hl, hs⟩
      have hpass' : ∀ x, t + 1 ≤ x → x < 2 ^ e →
          (remainder d e (monicBits e x) (monicBits d c) != 0) = true := by
        intro x hx hx'
        exact hpass x (by omega) hx'
      obtain ⟨v, hv, hout⟩ :=
        ih (k - 1) (by omega) (t + 1) (by omega)
          (by omega) hpass' g.var
      refine ⟨u + v, ?_, ?_⟩
      · have hb := nonlast_divisor_budget d e hed
        have hmul : k * correctedPairEnvelope d e =
            (k - 1) * correctedPairEnvelope d e +
              correctedPairEnvelope d e := by
          conv_lhs => rw [show k = (k - 1) + 1 by omega]
          ring
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
        change (run v g).l = some (.outer .success) ∧
          (run v g).stk 0 =
            CurrentAdditive.FieldMachineHelper.TrialCounterMachine.counterWord d c
        rw [hcfg]
        exact hout

#print axioms passing_final_degree

end CurrentAdditive.FieldSearchCompletion
