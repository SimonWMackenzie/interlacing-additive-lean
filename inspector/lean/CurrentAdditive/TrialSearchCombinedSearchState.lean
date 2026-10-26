import CurrentAdditive.TrialSearchCombinedOuterExact
import CurrentAdditive.TrialTailPrinterBridge
import CurrentAdditive.TrialSearchControllerBridge

/-! The physical stack invariant at each divisor-test boundary. -/

namespace CurrentAdditive.FieldMachineHelper.TrialSearchCombinedSearchState

set_option maxHeartbeats 1000000

open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedCallback
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedOuterLift (boundary)
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedOuterExact
open CurrentAdditive.FieldMachineHelper.TrialCounterMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchControllerBridge
open CurrentAdditive.FieldMachineHelper.TrialDividerTotal (divisionClock)
open CurrentAdditive.FiniteFieldConstructor.TrialSearch (monicBits remainder)

namespace Outer
export CurrentAdditive.FieldMachineHelper.TrialSearchControllerMachine
  (Label Config Control bank cfg run run_after_passing_nonlast_divisor)
end Outer

def searchBank (d c e t : Nat) : Fin 12 → List Bool :=
  Outer.bank (counterWord d c) (counterWord e t)
    (List.replicate (d - e) true) (fun _ => [])
    (List.replicate (d / 2 - e + 1) true)
    (List.replicate (e - 1) true)
    (List.replicate (e - 1) true) []

theorem searchBank_stacks (d c e t : Nat) :
    searchBank d c e t 0 = counterWord d c ∧
    searchBank d c e t 1 = counterWord e t ∧
    searchBank d c e t 2 = List.replicate (d - e) true ∧
    searchBank d c e t 3 = [] ∧
    searchBank d c e t 4 = [] ∧
    searchBank d c e t 5 = [] ∧
    searchBank d c e t 6 = [] ∧
    searchBank d c e t 7 = [] := by
  simp [searchBank, Outer.bank]

theorem combined_pass_nonlast_divisor
    (d c e t : Nat) (he : e ≤ d) (hc : c < 2 ^ d)
    (ht : t + 1 < 2 ^ e)
    (hpass : (remainder d e (monicBits e t) (monicBits d c) != 0) = true)
    (base : Registers) :
    ∃ steps ≤ 1 + 4 * d + 6 +
        (divisionClock e (d - e + 1) + 2 * e + 3) + (2 * e + 3),
      let g := run steps
        ⟨some (.outer .test), base, searchBank d c e t⟩
      g.l = some (.outer .test) ∧
      g.stk = searchBank d c e (t + 1) := by
  let S := searchBank d c e t
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := searchBank_stacks d c e t
  have ht' : t < 2 ^ e := by omega
  obtain ⟨u, hu, hcallback⟩ :=
    combined_test_from_controller d e c t he hc ht' base S
      h0 h1 h2 h3 h4 h5 h6 h7
  let g₁ := run u ⟨some (.outer .test), base, S⟩
  change g₁.l = _ ∧ _ at hcallback
  rcases hcallback with
    ⟨hl₁, hb₁, hs₁0, hs₁1, hs₁2, hs₁3, hs₁4, hs₁5, hs₁6, hs₁7, hf₁⟩
  have hstack₁ : g₁.stk = S := by
    funext i
    fin_cases i
    · exact hs₁0
    · exact hs₁1
    · exact hs₁2
    · exact hs₁3.trans h3.symm
    · exact hs₁4.trans h4.symm
    · exact hs₁5.trans h5.symm
    · exact hs₁6.trans h6.symm
    · exact hs₁7.trans h7.symm
    · exact hf₁ 8 (by decide)
    · exact hf₁ 9 (by decide)
    · exact hf₁ 10 (by decide)
    · exact hf₁ 11 (by decide)
  have hresult : g₁.var.outer.1 = true := by rw [hb₁, hpass]
  have houter : g₁.var.outer =
      (true, g₁.var.outer.2.1, g₁.var.outer.2.2) := by
    rcases h : g₁.var.outer with ⟨b, carry, bit⟩
    simp [h] at hresult ⊢
    cases b <;> simp_all
  have hcarry := increment_counter_carry_nonlast e t ht
  have hbranch := Outer.run_after_passing_nonlast_divisor
    (counterWord d c) (counterWord e t) (List.replicate (d - e) true)
    (fun _ => []) (List.replicate (d / 2 - e + 1) true)
    (List.replicate (e - 1) true) (List.replicate (e - 1) true)
    g₁.var.outer.2.1 g₁.var.outer.2.2 hcarry
  rw [← houter] at hbranch
  have hlocal :
      (Outer.run (2 * e + 3)
        ⟨some .afterTest, g₁.var.outer, g₁.stk⟩).l = some .test := by
    rw [hstack₁]
    simpa [S, searchBank, Outer.cfg, counterWord_length] using
      congrArg (fun q : Outer.Config => q.l) hbranch
  have hglobal := combined_controller_exact g₁.var g₁.stk
    .afterTest .test (2 * e + 3) hlocal (by trivial)
  refine ⟨u + (2 * e + 3), by omega, ?_⟩
  have htime : run (u + (2 * e + 3))
      ⟨some (.outer .test), base, S⟩ =
        run (2 * e + 3) ⟨some (.outer .afterTest), g₁.var, g₁.stk⟩ := by
    rw [TrialSearchCombinedMachine.run_add]
    change run (2 * e + 3) g₁ = _
    have hcfg₁ : g₁ = ⟨some (.outer .afterTest), g₁.var, g₁.stk⟩ := by
      rcases g₁ with ⟨l, v, T⟩
      change l = some (.outer .afterTest) at hl₁
      cases hl₁
      rfl
    rw [hcfg₁]
  rw [htime, hglobal]
  refine ⟨rfl, ?_⟩
  have hstate : (Outer.run (2 * e + 3)
      ⟨some .afterTest, g₁.var.outer, g₁.stk⟩).stk =
      searchBank d c e (t + 1) := by
    rw [hstack₁]
    simpa [S, searchBank, Outer.cfg, counterWord_length,
      counterWord_increment e t] using
      congrArg (fun q : Outer.Config => q.stk) hbranch
  exact hstate

#print axioms combined_pass_nonlast_divisor

end CurrentAdditive.FieldMachineHelper.TrialSearchCombinedSearchState
