import CurrentAdditive.TrialSearchCombinedPrep
import CurrentAdditive.TrialDividerTotal

/-! Exact long-division phase inside the single combined trial-search program. -/

namespace CurrentAdditive.FieldMachineHelper.TrialSearchCombinedDivide

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedRun
open CurrentAdditive.FieldMachineHelper.TrialDividerTotal
open CurrentAdditive.FieldMachineHelper.DivisionBitStep (bitsBE)
open CurrentAdditive.FiniteFieldConstructor.TrialSearch (monicBits remainder)

theorem divideStack_injective : Function.Injective divideStack := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [divideStack] at h ⊢

theorem divider_phase_in_combined_program
    (d e tail dividend : Nat) (he : e ≤ d) (htail : tail < 2 ^ e)
    (base : Registers) (S : Fin 12 → List Bool)
    (hcontrol : base.divide = (false, none, none))
    (hacc : S 3 = bitsBE (d + 1) dividend)
    (hdiv : S 4 = divisorWord e tail (d - e + 1))
    (hcount : S 5 = List.replicate (d - e + 1) true)
    (hscratchAcc : S 6 = []) (hscratchDiv : S 7 = []) :
    ∃ (bFinal : Bool) (t : Nat),
      t ≤ divisionClock e (d - e + 1) + 1 ∧
      phaseRel divideStack Label.divide (.zero .scan)
        (fun r v => {r with divide := v})
        (fun r => {r with zero := (false, none)})
        base S
        (CurrentAdditive.FieldMachineHelper.TrialDividerMachine.cfg none
          (bFinal, none, none)
          (bitsBE e (remainder d e (monicBits e tail) dividend))
          (divisorWord e tail 0) [] [] [])
        (TrialSearchCombinedMachine.run t
          ⟨some (.divide .next), base, S⟩) := by
  let n := divisionClock e (d - e + 1) + 1
  have hprogram (l : CurrentAdditive.FieldMachineHelper.TrialDividerMachine.Label) :
      TrialSearchCombinedMachine.program (.divide l) =
      embedStmt divideStack Label.divide (.zero .scan)
        (fun r => r.divide) (fun r v => {r with divide := v})
        (fun r => {r with zero := (false, none)})
        (CurrentAdditive.FieldMachineHelper.TrialDividerMachine.program l) := rfl
  have hprojection :
      (fun k : Fin 5 => S (divideStack k)) =
      CurrentAdditive.FieldMachineHelper.TrialDividerMachine.bank
        (bitsBE (d + 1) dividend)
        (divisorWord e tail (d - e + 1)) [] []
        (List.replicate (d - e + 1) true) := by
    funext k
    fin_cases k <;>
      simp [divideStack,
        CurrentAdditive.FieldMachineHelper.TrialDividerMachine.bank,
        hacc, hdiv, hcount, hscratchAcc, hscratchDiv]
  obtain ⟨bFinal, hrun⟩ := divider_remainder d e tail dividend he htail
  have hlocal :
      ((((advance CurrentAdditive.FieldMachineHelper.TrialDividerMachine.program)^[n])
        (⟨some CurrentAdditive.FieldMachineHelper.TrialDividerMachine.Label.next,
          base.divide, fun k => S (divideStack k)⟩ :
          CurrentAdditive.FieldMachineHelper.TrialDividerMachine.Config)).l = none) := by
    simpa [CurrentAdditive.FieldMachineHelper.TrialDividerMachine.run,
      CurrentAdditive.FieldMachineHelper.TrialDividerMachine.cfg,
      hcontrol, hprojection] using congrArg TM2.Cfg.l hrun
  obtain ⟨t, ht, hrel⟩ :=
    phaseRel_halts_within divideStack divideStack_injective
      Label.divide (.zero .scan)
      (fun r => r.divide) (fun r v => {r with divide := v})
      (fun r => {r with zero := (false, none)})
      (by intro r v; rfl) (by intro r v w; rfl)
      (by intro r; cases r; rfl) (by intro r; rfl)
      CurrentAdditive.FieldMachineHelper.TrialDividerMachine.program
      TrialSearchCombinedMachine.program hprogram base S .next n hlocal
  refine ⟨bFinal, t, ht, ?_⟩
  change ((advance CurrentAdditive.FieldMachineHelper.TrialDividerMachine.program)^[n])
    (CurrentAdditive.FieldMachineHelper.TrialDividerMachine.cfg
      (some .next) (false, none, none)
      (bitsBE (d + 1) dividend)
      (divisorWord e tail (d - e + 1)) [] []
      (List.replicate (d - e + 1) true)) = _ at hrun
  have hstart :
      (CurrentAdditive.FieldMachineHelper.TrialDividerMachine.cfg
        (some .next) (false, none, none)
        (bitsBE (d + 1) dividend)
        (divisorWord e tail (d - e + 1)) [] []
        (List.replicate (d - e + 1) true)) =
      (⟨some CurrentAdditive.FieldMachineHelper.TrialDividerMachine.Label.next,
        base.divide, fun k => S (divideStack k)⟩ :
          CurrentAdditive.FieldMachineHelper.TrialDividerMachine.Config) := by
    simp [CurrentAdditive.FieldMachineHelper.TrialDividerMachine.cfg,
      hcontrol, hprojection]
  rw [hstart] at hrun
  exact hrun ▸ hrel

#print axioms divider_phase_in_combined_program

end CurrentAdditive.FieldMachineHelper.TrialSearchCombinedDivide
