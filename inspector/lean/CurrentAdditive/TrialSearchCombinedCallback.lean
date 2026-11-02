import CurrentAdditive.TrialSearchCombinedPrepContext
import CurrentAdditive.TrialSearchCombinedPairFull

/-! A complete physical test callback in the shared search machine. -/

namespace CurrentAdditive.FieldMachineHelper.TrialSearchCombinedCallback

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedPrepContext
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedPairFull
open CurrentAdditive.FieldMachineHelper.TrialCounterMachine (counterWord)
open CurrentAdditive.FieldMachineHelper.TrialDividerTotal (divisionClock)
open CurrentAdditive.FiniteFieldConstructor.TrialSearch (monicBits remainder)

theorem combined_test_callback
    (d e candidateTail divisorTail : Nat)
    (he : e ≤ d) (hc : candidateTail < 2 ^ d)
    (hv : divisorTail < 2 ^ e)
    (base : Registers) (S : Fin 12 → List Bool)
    (hprep : base.prep = none)
    (h0 : S 0 = counterWord d candidateTail)
    (h1 : S 1 = counterWord e divisorTail)
    (h2 : S 2 = List.replicate (d - e) true)
    (h3 : S 3 = []) (h4 : S 4 = [])
    (h5 : S 5 = []) (h6 : S 6 = []) (h7 : S 7 = []) :
    ∃ t ≤ 4 * d + 6 + (divisionClock e (d - e + 1) + 2 * e + 3),
      let g := run t ⟨some (.prep .shiftScan), base, S⟩
      g.l = some (.outer .afterTest) ∧
      g.var.outer.1 =
        (remainder d e (monicBits e divisorTail)
          (monicBits d candidateTail) != 0) ∧
      g.stk 0 = S 0 ∧ g.stk 1 = S 1 ∧ g.stk 2 = S 2 ∧
      g.stk 3 = [] ∧ g.stk 4 = [] ∧ g.stk 5 = [] ∧
      g.stk 6 = [] ∧ g.stk 7 = [] ∧
      (∀ i : Fin 12, 8 ≤ i.val → g.stk i = S i) := by
  obtain ⟨t₁, ht₁, hprepRun⟩ := prep_context_result d e candidateTail
    divisorTail he hc hv base S hprep h0 h1 h2 h3 h4 h5 h6
  let g₁ := run t₁ ⟨some (.prep .shiftScan), base, S⟩
  change g₁.l = _ ∧ _ at hprepRun
  rcases hprepRun with
    ⟨hl₁, hc₁, hs₁0, hs₁1, hs₁2, hs₁3, hs₁4, hs₁5, hs₁6, hf₁⟩
  have hs₁7 : g₁.stk 7 = [] := by rw [hf₁ 7 (by decide), h7]
  have hcfg₁ : g₁ = ⟨some (.divide .next), g₁.var, g₁.stk⟩ := by
    rcases g₁ with ⟨l, v, T⟩
    change l = some (.divide .next) at hl₁
    cases hl₁
    rfl
  obtain ⟨t₂, ht₂, hpairRun⟩ :=
    combined_one_divisor_test_full d e divisorTail candidateTail
      he hv hc g₁.var g₁.stk hc₁ hs₁3 hs₁4 hs₁5 hs₁6 hs₁7
  let g₂ := run t₂ g₁
  rw [← hcfg₁] at hpairRun
  change g₂.l = _ ∧ _ at hpairRun
  rcases hpairRun with
    ⟨hl₂, hb₂, hs₂0, hs₂1, hs₂2, hs₂3, hs₂4, hs₂5, hs₂6, hs₂7, hf₂⟩
  refine ⟨t₁ + t₂, by omega, ?_⟩
  have htotal : run (t₁ + t₂) ⟨some (.prep .shiftScan), base, S⟩ = g₂ := by
    rw [TrialSearchCombinedMachine.run_add]
  rw [htotal]
  refine ⟨hl₂, hb₂, ?_, ?_, ?_, hs₂3, hs₂4, hs₂5, hs₂6, hs₂7, ?_⟩
  · rw [hs₂0, hs₁0, h0]
  · rw [hs₂1, hs₁1, h1]
  · rw [hs₂2, hs₁2, h2]
  · intro i hi
    rw [hf₂ i hi]
    exact hf₁ i (by omega)

#print axioms combined_test_callback

theorem test_entry_step (base : Registers) (S : Fin 12 → List Bool) :
    TM2.step program ⟨some (.outer .test), base, S⟩ =
      some ⟨some (.prep .shiftScan), {base with prep := none}, S⟩ := by
  simp [TM2.step, TM2.stepAux, program, embedStmt,
    CurrentAdditive.FieldMachineHelper.TrialSearchControllerMachine.program]

theorem combined_test_from_controller
    (d e candidateTail divisorTail : Nat)
    (he : e ≤ d) (hc : candidateTail < 2 ^ d)
    (hv : divisorTail < 2 ^ e)
    (base : Registers) (S : Fin 12 → List Bool)
    (h0 : S 0 = counterWord d candidateTail)
    (h1 : S 1 = counterWord e divisorTail)
    (h2 : S 2 = List.replicate (d - e) true)
    (h3 : S 3 = []) (h4 : S 4 = [])
    (h5 : S 5 = []) (h6 : S 6 = []) (h7 : S 7 = []) :
    ∃ t ≤ 1 + 4 * d + 6 +
        (divisionClock e (d - e + 1) + 2 * e + 3),
      let g := run t ⟨some (.outer .test), base, S⟩
      g.l = some (.outer .afterTest) ∧
      g.var.outer.1 =
        (remainder d e (monicBits e divisorTail)
          (monicBits d candidateTail) != 0) ∧
      g.stk 0 = S 0 ∧ g.stk 1 = S 1 ∧ g.stk 2 = S 2 ∧
      g.stk 3 = [] ∧ g.stk 4 = [] ∧ g.stk 5 = [] ∧
      g.stk 6 = [] ∧ g.stk 7 = [] ∧
      (∀ i : Fin 12, 8 ≤ i.val → g.stk i = S i) := by
  obtain ⟨u, hu, hout⟩ := combined_test_callback d e candidateTail
    divisorTail he hc hv {base with prep := none} S
    (by rfl) h0 h1 h2 h3 h4 h5 h6 h7
  refine ⟨1 + u, by omega, ?_⟩
  have hfirst : run 1 ⟨some (.outer .test), base, S⟩ =
      ⟨some (.prep .shiftScan), {base with prep := none}, S⟩ := by
    simpa [run, advance] using test_entry_step base S
  rw [TrialSearchCombinedMachine.run_add, hfirst]
  exact hout

#print axioms combined_test_from_controller

end CurrentAdditive.FieldMachineHelper.TrialSearchCombinedCallback
