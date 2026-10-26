import CurrentAdditive.TrialSearchCombinedDivide
import CurrentAdditive.TrialDivisorTest

/-! Exact zero-scan phase inside the single combined trial-search program. -/

namespace CurrentAdditive.FieldMachineHelper.TrialSearchCombinedZero

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedRun
open CurrentAdditive.FieldMachineHelper.ZeroWordTest

theorem zeroStack_injective : Function.Injective zeroStack := by
  intro a b _
  fin_cases a
  fin_cases b
  rfl

theorem zero_phase_in_combined_program
    (word : List Bool) (base : Registers) (S : Fin 12 → List Bool)
    (hcontrol : base.zero = (false, none)) (hword : S 3 = word) :
    ∃ t ≤ word.length + 1,
      phaseRel zeroStack Label.zero .clearDivisor
        (fun r v => {r with zero := v}) id base S
        (CurrentAdditive.FieldMachineHelper.ZeroWordTest.cfg none
          (word.any id, none) [])
        (TrialSearchCombinedMachine.run t
          ⟨some (.zero .scan), base, S⟩) := by
  let n := word.length + 1
  have hprogram (l : CurrentAdditive.FieldMachineHelper.ZeroWordTest.Label) :
      TrialSearchCombinedMachine.program (.zero l) =
      embedStmt zeroStack Label.zero .clearDivisor
        (fun r => r.zero) (fun r v => {r with zero := v}) id
        (CurrentAdditive.FieldMachineHelper.ZeroWordTest.program l) := rfl
  have hprojection : (fun k : Fin 1 => S (zeroStack k)) = fun _ => word := by
    funext k
    fin_cases k
    exact hword
  have hrun := ZeroWordTest.run_correct false none word
  have hlocal :
      ((((advance ZeroWordTest.program)^[n])
        (⟨some ZeroWordTest.Label.scan, base.zero,
          fun k => S (zeroStack k)⟩ : ZeroWordTest.Config)).l = none) := by
    simpa [ZeroWordTest.run, ZeroWordTest.cfg, hcontrol, hprojection]
      using congrArg TM2.Cfg.l hrun
  obtain ⟨t, ht, hrel⟩ :=
    phaseRel_halts_within zeroStack zeroStack_injective
      Label.zero .clearDivisor
      (fun r => r.zero) (fun r v => {r with zero := v}) id
      (by intro r v; rfl) (by intro r v w; rfl)
      (by intro r; cases r; rfl) (by intro r; rfl)
      ZeroWordTest.program TrialSearchCombinedMachine.program
      hprogram base S .scan n hlocal
  refine ⟨t, ht, ?_⟩
  change ((advance ZeroWordTest.program)^[n])
    (ZeroWordTest.cfg (some .scan) (false, none) word) = _ at hrun
  have hstart :
      ZeroWordTest.cfg (some .scan) (false, none) word =
      (⟨some ZeroWordTest.Label.scan, base.zero,
        fun k => S (zeroStack k)⟩ : ZeroWordTest.Config) := by
    simp [ZeroWordTest.cfg, hcontrol, hprojection]
  rw [hstart] at hrun
  exact hrun ▸ hrel

#print axioms zero_phase_in_combined_program

end CurrentAdditive.FieldMachineHelper.TrialSearchCombinedZero
