import CurrentAdditive.CanonicalAmbientDegreeInputs
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! Physical source-to-width handoff on the common ambient bank. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.YaoMachine

def widthHPlace (t N : ℕ) : Fin 3 ↪ Cell t N :=
  ⟨![.source (sN 6), .width 0, .copyScratch 0], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩

def widthKPlace (t N : ℕ) : Fin 3 ↪ Cell t N :=
  ⟨![.source (sN 9), .width 1, .copyScratch 0], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩

def widthInputProgram (t N : ℕ) :=
  BitMachineRawSequence.program
    (MatrixStage4ScalarPreparationOps.copyProgram (widthHPlace t N))
    (MatrixStage4ScalarPreparationOps.copyProgram (widthKPlace t N))
    BitMachineCopy.Label.scan none none

theorem physical_width_inputs (t N H K : ℕ) (S : Cell t N → List Bool)
    (hH : S (.source (sN 6)) = List.replicate H true)
    (hK : S (.source (sN 9)) = List.replicate K true)
    (hwidth0 : S (.width 0) = [])
    (hwidth1 : S (.width 1) = [])
    (hscratch : S (.copyScratch 0) = []) :
    ∃ steps ≤ (2*H+2) + (2*K+2) + 1,
      ((advance (widthInputProgram t N))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, none), S⟩ : TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
        ⟨none, (none, none),
          Function.update (Function.update S (.width 0)
            (List.replicate H true)) (.width 1) (List.replicate K true)⟩ := by
  let S1 := Function.update S (.width 0) (List.replicate H true)
  let S2 := Function.update S1 (.width 1) (List.replicate K true)
  have hr1 := MatrixStage4ScalarPreparationOps.copy_run (widthHPlace t N) S hscratch
  have hr1' : ((advance (MatrixStage4ScalarPreparationOps.copyProgram (widthHPlace t N)))^[2*H+2])
      (⟨some BitMachineCopy.Label.scan, none, S⟩ : TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
      ⟨none, none, S1⟩ := by
    simpa [widthHPlace, S1, hH, hwidth0] using hr1
  have hr2 := MatrixStage4ScalarPreparationOps.copy_run (widthKPlace t N) S1
    (by simp [widthKPlace, S1, hscratch])
  have hr2' : ((advance (MatrixStage4ScalarPreparationOps.copyProgram (widthKPlace t N)))^[2*K+2])
      (⟨some BitMachineCopy.Label.scan, none, S1⟩ : TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
      ⟨none, none, S2⟩ := by
    simpa [widthKPlace, S2, S1, hK, hwidth1] using hr2
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (MatrixStage4ScalarPreparationOps.copyProgram (widthHPlace t N))
    (MatrixStage4ScalarPreparationOps.copyProgram (widthKPlace t N))
    BitMachineCopy.Label.scan BitMachineCopy.Label.scan
    none none none none S S1 S2 (2*H+2) (2*K+2) hr1' hr2'
  exact ⟨steps, by omega, by simpa [widthInputProgram, S2, S1] using hrun⟩

#print axioms physical_width_inputs

def widthStage (t N : ℕ) :=
  fun l => stackStmt (widthEmbed t N) (CanonicalWidthMultiply.widthProgram l)

theorem physical_ambient_width (t N H K : ℕ) (S : Cell t N → List Bool)
    (hlocal : ∀ i : Fin 8, S (.width i) = CanonicalWidthMultiply.initial H K i) :
    ∃ steps ≤ (2 * K + 2) + 2 +
        MatrixAddressMachine.exactTime H (K + 1) 0 + 2,
      ((advance (widthStage t N))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, ((), false)), S⟩ : TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
        stackCfg (widthEmbed t N) S
          (⟨none, (none, ((), false)),
            Function.update (Function.update
              (CanonicalWidthMultiply.initial H K) 2
              (List.replicate (K + 1) true)) 3
              (List.replicate (H * (K + 1)) true)⟩ :
                TM2.Cfg (fun _ : Fin 8 => Bool) _ _) := by
  obtain ⟨steps, hsteps, hrun⟩ := CanonicalWidthMultiply.physical_width H K
  have hbank := bank_eq_self (widthEmbed t N) S
    (CanonicalWidthMultiply.initial H K) (by intro i; exact (hlocal i).symm)
  refine ⟨steps, hsteps, ?_⟩
  have hrun' := congrArg (stackCfg (widthEmbed t N) S) hrun
  rw [← EthInapproximability.CurrentPaper.BitMachineStackRun.run] at hrun'
  simpa [widthStage, stackCfg, hbank] using hrun'

#print axioms physical_ambient_width

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
