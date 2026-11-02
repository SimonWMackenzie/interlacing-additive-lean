import CurrentAdditive.TrialSearchCombinedCleanup

/-!
One whole physical divisor test in the combined twelve-stack program:
long division, remainder zero scan, and clearing the stale divisor word.
The result reaches the outer controller's `afterTest` label.
-/

namespace CurrentAdditive.FieldMachineHelper.TrialSearchCombinedPair

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedRun
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedSimulation (carriedLabel)
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedDivide
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedZero
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedCleanup
open CurrentAdditive.FieldMachineHelper.TrialDividerTotal
open CurrentAdditive.FieldMachineHelper.DivisionBitStep (bitsBE bitsBE_length)
open CurrentAdditive.FiniteFieldConstructor.TrialSearch (monicBits remainder)

private theorem cfg_eq_of_label (c : Config) (l : Label)
    (h : c.l = some l) : c = ⟨some l, c.var, c.stk⟩ := by
  rcases c with ⟨label, regs, bank⟩
  cases h
  rfl

theorem divisorWord_zero_length (e tail : Nat) :
    (divisorWord e tail 0).length = e := by
  simp [divisorWord, bitsBE_length, List.length_dropLast]

theorem remainder_word_any_eq_test
    (d e tail dividendTail : Nat)
    (he : e ≤ d) (htail : tail < 2 ^ e)
    (hdividend : dividendTail < 2 ^ d) :
    (bitsBE e (remainder d e (monicBits e tail)
      (monicBits d dividendTail))).any id =
      (remainder d e (monicBits e tail)
        (monicBits d dividendTail) != 0) := by
  have hp := CurrentAdditive.FieldMachineHelper.TrialDivisorTest.physical_remainder_nonzero_test
    d e tail dividendTail he htail hdividend
  have hz := CurrentAdditive.FieldMachineHelper.ZeroWordTest.run_correct
    false none (bitsBE e (remainder d e (monicBits e tail)
      (monicBits d dividendTail)))
  have hz' : CurrentAdditive.FieldMachineHelper.ZeroWordTest.run (e + 1)
      (CurrentAdditive.FieldMachineHelper.ZeroWordTest.cfg (some .scan)
        (false, none) (bitsBE e (remainder d e (monicBits e tail)
          (monicBits d dividendTail)))) =
      CurrentAdditive.FieldMachineHelper.ZeroWordTest.cfg none
        ((bitsBE e (remainder d e (monicBits e tail)
          (monicBits d dividendTail))).any id, none) [] := by
    simpa [bitsBE_length] using hz
  rw [hz'] at hp
  have hv := congrArg (fun c : CurrentAdditive.FieldMachineHelper.ZeroWordTest.Config => c.var.1) hp
  simpa [CurrentAdditive.FieldMachineHelper.ZeroWordTest.cfg] using hv

theorem combined_one_divisor_test
    (d e divisorTail candidateTail : Nat)
    (he : e ≤ d) (hdivisor : divisorTail < 2 ^ e)
    (hcandidate : candidateTail < 2 ^ d)
    (base : Registers) (S : Fin 12 → List Bool)
    (hcontrol : base.divide = (false, none, none))
    (hacc : S 3 = bitsBE (d + 1) (monicBits d candidateTail))
    (hdiv : S 4 = divisorWord e divisorTail (d - e + 1))
    (hcount : S 5 = List.replicate (d - e + 1) true)
    (hscratchAcc : S 6 = []) (hscratchDiv : S 7 = []) :
    ∃ t ≤ divisionClock e (d - e + 1) + 2 * e + 3,
      let g := TrialSearchCombinedMachine.run t
        ⟨some (.divide .next), base, S⟩
      g.l = some (.outer .afterTest) ∧
      g.var.outer.1 =
        (remainder d e (monicBits e divisorTail)
          (monicBits d candidateTail) != 0) ∧
      g.stk 0 = S 0 ∧ g.stk 1 = S 1 ∧ g.stk 2 = S 2 ∧
      g.stk 3 = [] ∧ g.stk 4 = [] ∧ g.stk 5 = [] ∧
      g.stk 6 = [] ∧ g.stk 7 = [] := by
  let remWord := bitsBE e (remainder d e (monicBits e divisorTail)
    (monicBits d candidateTail))
  let divWord := divisorWord e divisorTail 0
  let start : Config := ⟨some (.divide .next), base, S⟩
  obtain ⟨bFinal, t₁, ht₁, hrel₁⟩ :=
    divider_phase_in_combined_program d e divisorTail
      (monicBits d candidateTail) he hdivisor base S
      hcontrol hacc hdiv hcount hscratchAcc hscratchDiv
  let g₁ := TrialSearchCombinedMachine.run t₁ start
  change phaseRel divideStack Label.divide (.zero .scan)
    (fun r v => {r with divide := v})
    (fun r => {r with zero := (false, none)}) base S
    (CurrentAdditive.FieldMachineHelper.TrialDividerMachine.cfg none
      (bFinal, none, none) remWord divWord [] [] []) g₁ at hrel₁
  rcases hrel₁ with ⟨hl₁, hv₁, hs₁, hf₁⟩
  have hlabel₁ : g₁.l = some (.zero .scan) := by
    simpa [carriedLabel] using hl₁
  have hzero₁ : g₁.var.zero = (false, none) := by
    simpa [CurrentAdditive.FieldMachineHelper.TrialDividerMachine.cfg]
      using congrArg Registers.zero hv₁
  have hstack₁3 : g₁.stk 3 = remWord := by
    simpa [divideStack, CurrentAdditive.FieldMachineHelper.TrialDividerMachine.cfg,
      CurrentAdditive.FieldMachineHelper.TrialDividerMachine.bank]
      using hs₁ (0 : Fin 5)
  have hstack₁4 : g₁.stk 4 = divWord := by
    simpa [divideStack, CurrentAdditive.FieldMachineHelper.TrialDividerMachine.cfg,
      CurrentAdditive.FieldMachineHelper.TrialDividerMachine.bank]
      using hs₁ (1 : Fin 5)
  have hstack₁5 : g₁.stk 5 = [] := by
    simpa [divideStack, CurrentAdditive.FieldMachineHelper.TrialDividerMachine.cfg,
      CurrentAdditive.FieldMachineHelper.TrialDividerMachine.bank]
      using hs₁ (4 : Fin 5)
  have hstack₁6 : g₁.stk 6 = [] := by
    simpa [divideStack, CurrentAdditive.FieldMachineHelper.TrialDividerMachine.cfg,
      CurrentAdditive.FieldMachineHelper.TrialDividerMachine.bank]
      using hs₁ (2 : Fin 5)
  have hstack₁7 : g₁.stk 7 = [] := by
    simpa [divideStack, CurrentAdditive.FieldMachineHelper.TrialDividerMachine.cfg,
      CurrentAdditive.FieldMachineHelper.TrialDividerMachine.bank]
      using hs₁ (3 : Fin 5)
  have houtside₁ (i : Fin 12) (hi : i = 0 ∨ i = 1 ∨ i = 2) :
      g₁.stk i = S i := by
    apply hf₁ i
    intro k hk
    rcases hi with rfl | rfl | rfl <;> fin_cases k <;>
      simp [divideStack] at hk
  have hconfig₁ : g₁ = ⟨some (.zero .scan), g₁.var, g₁.stk⟩ := by
    exact cfg_eq_of_label g₁ (.zero .scan) hlabel₁
  obtain ⟨t₂, ht₂, hrel₂⟩ :=
    zero_phase_in_combined_program remWord g₁.var g₁.stk
      hzero₁ hstack₁3
  let g₂ := TrialSearchCombinedMachine.run t₂ g₁
  rw [← hconfig₁] at hrel₂
  change phaseRel zeroStack Label.zero .clearDivisor
    (fun r v => {r with zero := v}) id g₁.var g₁.stk
    (CurrentAdditive.FieldMachineHelper.ZeroWordTest.cfg none
      (remWord.any id, none) []) g₂ at hrel₂
  rcases hrel₂ with ⟨hl₂, hv₂, hs₂, hf₂⟩
  have hlabel₂ : g₂.l = some .clearDivisor := by
    simpa [carriedLabel] using hl₂
  have hzero₂ : g₂.var.zero = (remWord.any id, none) := by
    simpa [CurrentAdditive.FieldMachineHelper.ZeroWordTest.cfg]
      using congrArg Registers.zero hv₂
  have hstack₂3 : g₂.stk 3 = [] := by
    simpa [zeroStack, CurrentAdditive.FieldMachineHelper.ZeroWordTest.cfg]
      using hs₂ (0 : Fin 1)
  have hstack₂4 : g₂.stk 4 = divWord := by
    rw [hf₂ 4 (by intro k hk; fin_cases k; simp [zeroStack] at hk)]
    exact hstack₁4
  have houtside₂ (i : Fin 12) (hi : i ≠ 3) : g₂.stk i = g₁.stk i := by
    exact hf₂ i (by
      intro k hk
      have hz : zeroStack k = (3 : Fin 12) := by fin_cases k; rfl
      rw [hz] at hk
      exact hi hk.symm)
  have hconfig₂ : g₂ = ⟨some .clearDivisor, g₂.var, g₂.stk⟩ := by
    exact cfg_eq_of_label g₂ .clearDivisor hlabel₂
  have hclean := clear_divisor_run g₂.var g₂.stk divWord hstack₂4
  rw [← hconfig₂] at hclean
  let t₃ := divWord.length + 1
  let g₃ := TrialSearchCombinedMachine.run t₃ g₂
  have hg₃ : g₃ =
      ⟨some (.outer .afterTest),
        {g₂.var with outer := (g₂.var.zero.1, g₂.var.outer.2.1, none)},
        Function.update g₂.stk 4 []⟩ := hclean
  have hresult : remWord.any id =
      (remainder d e (monicBits e divisorTail)
        (monicBits d candidateTail) != 0) :=
    remainder_word_any_eq_test d e divisorTail candidateTail
      he hdivisor hcandidate
  have hbound : t₁ + t₂ + t₃ ≤
      divisionClock e (d - e + 1) + 2 * e + 3 := by
    have hw : remWord.length = e := bitsBE_length e _
    have hdw : divWord.length = e := divisorWord_zero_length e divisorTail
    dsimp [t₃]
    omega
  refine ⟨t₁ + t₂ + t₃, hbound, ?_⟩
  have htime : TrialSearchCombinedMachine.run (t₁ + t₂ + t₃) start = g₃ := by
    rw [TrialSearchCombinedMachine.run_add (t₁ + t₂) t₃,
      TrialSearchCombinedMachine.run_add t₁ t₂]
  rw [htime]
  change g₃.l = _ ∧ _
  rw [hg₃]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hzero₂] using hresult
  · change (Function.update g₂.stk 4 []) 0 = S 0
    rw [Function.update_of_ne (by decide : (0 : Fin 12) ≠ 4)]
    rw [houtside₂ 0 (by decide), houtside₁ 0 (Or.inl rfl)]
  · change (Function.update g₂.stk 4 []) 1 = S 1
    rw [Function.update_of_ne (by decide : (1 : Fin 12) ≠ 4)]
    rw [houtside₂ 1 (by decide), houtside₁ 1 (Or.inr (Or.inl rfl))]
  · change (Function.update g₂.stk 4 []) 2 = S 2
    rw [Function.update_of_ne (by decide : (2 : Fin 12) ≠ 4)]
    rw [houtside₂ 2 (by decide), houtside₁ 2 (Or.inr (Or.inr rfl))]
  · change (Function.update g₂.stk 4 []) 3 = []
    rw [Function.update_of_ne (by decide : (3 : Fin 12) ≠ 4)]
    exact hstack₂3
  · simp
  · change (Function.update g₂.stk 4 []) 5 = []
    rw [Function.update_of_ne (by decide : (5 : Fin 12) ≠ 4)]
    rw [houtside₂ 5 (by decide)]
    exact hstack₁5
  · change (Function.update g₂.stk 4 []) 6 = []
    rw [Function.update_of_ne (by decide : (6 : Fin 12) ≠ 4)]
    rw [houtside₂ 6 (by decide)]
    exact hstack₁6
  · change (Function.update g₂.stk 4 []) 7 = []
    rw [Function.update_of_ne (by decide : (7 : Fin 12) ≠ 4)]
    rw [houtside₂ 7 (by decide)]
    exact hstack₁7

#print axioms combined_one_divisor_test

#print axioms remainder_word_any_eq_test

end CurrentAdditive.FieldMachineHelper.TrialSearchCombinedPair
