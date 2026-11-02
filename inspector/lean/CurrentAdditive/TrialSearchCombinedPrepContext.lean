import CurrentAdditive.TrialSearchCombinedPair
import CurrentAdditive.TrialSearchCombinedOuterLift

/-! Physical preparation from arbitrary preserved outer-controller stacks. -/

namespace CurrentAdditive.FieldMachineHelper.TrialSearchCombinedPrepContext

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedRun
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedPrep
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedSimulation (carriedLabel)
open CurrentAdditive.FieldMachineHelper.TrialCounterMachine (counterWord)
open CurrentAdditive.FieldMachineHelper.TrialDividerTotal (divisorWord)
open CurrentAdditive.FieldMachineHelper.TrialInputPrepBridge
open CurrentAdditive.FiniteFieldConstructor.TrialSearch (monicBits)

theorem prep_phase_context
    (d e candidateTail divisorTail : Nat)
    (he : e ≤ d) (hc : candidateTail < 2 ^ d)
    (hv : divisorTail < 2 ^ e)
    (base : Registers) (S : Fin 12 → List Bool)
    (hprep : base.prep = none)
    (h0 : S 0 = counterWord d candidateTail)
    (h1 : S 1 = counterWord e divisorTail)
    (h2 : S 2 = List.replicate (d - e) true)
    (h3 : S 3 = []) (h4 : S 4 = [])
    (h5 : S 5 = []) (h6 : S 6 = []) :
    ∃ t ≤ 4 * d + 6,
      phaseRel prepStack Label.prep (.divide .next)
        (fun r v => {r with prep := v})
        (fun r => {r with divide := (false, none, none)})
        base S
        (CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.cfg none none
          (counterWord d candidateTail)
          (counterWord e divisorTail)
          (List.replicate (d - e) true)
          (CurrentAdditive.FieldMachineHelper.DivisionBitStep.bitsBE
            (d + 1) (monicBits d candidateTail))
          (divisorWord e divisorTail (d - e + 1))
          (List.replicate (d - e + 1) true) [])
        (run t ⟨some (.prep .shiftScan), base, S⟩) := by
  let candidate := counterWord d candidateTail
  let divisor := counterWord e divisorTail
  let shift := List.replicate (d - e) true
  have hproj : (fun k : Fin 7 => S (prepStack k)) =
      CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.bank
        candidate divisor shift [] [] [] [] := by
    funext k
    fin_cases k <;> simp [prepStack,
      CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.bank,
      candidate, divisor, shift, h0, h1, h2, h3, h4, h5, h6]
  have hprogram (l : CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.Label) :
      program (.prep l) =
        embedStmt prepStack Label.prep (.divide .next)
          (fun r => r.prep) (fun r v => {r with prep := v})
          (fun r => {r with divide := (false, none, none)})
          (CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.program l) := rfl
  have hlocal :
      ((((advance CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.program)^[4 * d + 6])
        (⟨some CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.Label.shiftScan,
          base.prep, fun k => S (prepStack k)⟩ :
          CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.Config)).l = none) := by
    rw [hprep, hproj]
    simpa [CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.run,
      CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.cfg] using
      congrArg TM2.Cfg.l (run_prepare_trial_input d e candidateTail divisorTail he hc hv)
  obtain ⟨t, ht, hrel⟩ :=
    phaseRel_halts_within prepStack prepStack_injective
      Label.prep (.divide .next)
      (fun r => r.prep) (fun r v => {r with prep := v})
      (fun r => {r with divide := (false, none, none)})
      (by intro r v; rfl) (by intro r v w; rfl)
      (by intro r; cases r; rfl) (by intro r; rfl)
      CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.program
      program hprogram base S .shiftScan (4 * d + 6) hlocal
  refine ⟨t, ht, ?_⟩
  have hrun := run_prepare_trial_input d e candidateTail divisorTail he hc hv
  change ((advance CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.program)^[4 * d + 6])
      (CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.cfg
        (some .shiftScan) none candidate divisor shift [] [] [] []) = _ at hrun
  rw [show CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.cfg
      (some .shiftScan) none candidate divisor shift [] [] [] [] =
      (⟨some CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.Label.shiftScan,
        base.prep, fun k => S (prepStack k)⟩ :
          CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.Config) from by
      simp [hprep, hproj, CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.cfg]] at hrun
  exact hrun ▸ hrel

#print axioms prep_phase_context

theorem prep_context_result
    (d e candidateTail divisorTail : Nat)
    (he : e ≤ d) (hc : candidateTail < 2 ^ d)
    (hv : divisorTail < 2 ^ e)
    (base : Registers) (S : Fin 12 → List Bool)
    (hprep : base.prep = none)
    (h0 : S 0 = counterWord d candidateTail)
    (h1 : S 1 = counterWord e divisorTail)
    (h2 : S 2 = List.replicate (d - e) true)
    (h3 : S 3 = []) (h4 : S 4 = [])
    (h5 : S 5 = []) (h6 : S 6 = []) :
    ∃ t ≤ 4 * d + 6,
      let g := run t ⟨some (.prep .shiftScan), base, S⟩
      g.l = some (.divide .next) ∧
      g.var.divide = (false, none, none) ∧
      g.stk 0 = counterWord d candidateTail ∧
      g.stk 1 = counterWord e divisorTail ∧
      g.stk 2 = List.replicate (d - e) true ∧
      g.stk 3 = CurrentAdditive.FieldMachineHelper.DivisionBitStep.bitsBE
        (d + 1) (monicBits d candidateTail) ∧
      g.stk 4 = divisorWord e divisorTail (d - e + 1) ∧
      g.stk 5 = List.replicate (d - e + 1) true ∧
      g.stk 6 = [] ∧
      (∀ i : Fin 12, 7 ≤ i.val → g.stk i = S i) := by
  obtain ⟨t, ht, hrel⟩ := prep_phase_context d e candidateTail divisorTail
    he hc hv base S hprep h0 h1 h2 h3 h4 h5 h6
  refine ⟨t, ht, ?_⟩
  rcases hrel with ⟨hl, hv, hs, hf⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [carriedLabel] using hl
  · simpa [CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.cfg]
      using congrArg Registers.divide hv
  · simpa [prepStack, CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.cfg,
      CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.bank]
      using hs (0 : Fin 7)
  · simpa [prepStack, CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.cfg,
      CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.bank]
      using hs (1 : Fin 7)
  · simpa [prepStack, CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.cfg,
      CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.bank]
      using hs (2 : Fin 7)
  · simpa [prepStack, CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.cfg,
      CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.bank]
      using hs (3 : Fin 7)
  · simpa [prepStack, CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.cfg,
      CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.bank]
      using hs (4 : Fin 7)
  · simpa [prepStack, CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.cfg,
      CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.bank]
      using hs (5 : Fin 7)
  · simpa [prepStack, CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.cfg,
      CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.bank]
      using hs (6 : Fin 7)
  · intro i hi
    apply hf i
    intro k hk
    have hv := congrArg Fin.val hk
    simp [prepStack] at hv
    omega

#print axioms prep_context_result

end CurrentAdditive.FieldMachineHelper.TrialSearchCombinedPrepContext
