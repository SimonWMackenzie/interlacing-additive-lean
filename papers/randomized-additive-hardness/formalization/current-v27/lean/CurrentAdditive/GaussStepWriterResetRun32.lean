import CurrentAdditive.GaussStepPivotJoinRun32

/-! Charged reset of the framing worker between pair and count writes. -/

namespace CurrentAdditive.GaussStepWriterResetRun32

noncomputable section

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding
open CurrentAdditive.GaussStepFields32

def cleared (S : Stack → List Bool) : Stack → List Bool :=
  BitMachineClearBank.cleared GaussWorkerReset32.bank S

theorem reset_phase (S : Stack → List Bool) :
    ∃ t ≤ GaussWorkerReset32.clock S+1,
      run t ⟨some (.resetWriter (.inl 0)),
        eResetWriter ((),none),S⟩ =
      ⟨some .afterResetWriter,eResetWriter ((),none),cleared S⟩ := by
  have hlocal : GaussWorkerReset32.run
      (GaussWorkerReset32.clock S+1)
      ⟨some (.inl 0),((),none),S⟩ =
      ⟨none,((),none),cleared S⟩ := by
    change ((advance GaussWorkerReset32.program)^[
      GaussWorkerReset32.clock S+1]) _ = _
    rw [Function.iterate_succ_apply',
      ← GaussWorkerReset32.run,
      GaussWorkerReset32.physical_reset]
    rfl
  obtain ⟨u,hu,hglobal⟩ :=
    GaussStepPhaseLift32.reset_writer_lift
      (⟨some (.inl 0),((),none),S⟩)
      (GaussWorkerReset32.clock S+1)
      (by rw [hlocal])
  exact ⟨u,hu,by simpa [BitMachineInline.cfg,hlocal] using hglobal⟩

theorem preserves (S : Stack → List Bool) (j : Stack)
    (h : j.val < 8 ∨ 16 ≤ j.val) : cleared S j = S j := by
  apply BitMachineClearBank.cleared_foreign GaussWorkerReset32.bank S j
  intro q hq
  have hv := congrArg Fin.val hq
  fin_cases q <;> simp [GaussWorkerReset32.bank] at hv <;>
    rcases h with hj | hj <;> omega

theorem worker_empty (S : Stack → List Bool)
    (j : Fin (SourceListMachineWriter.framingMachine false).stackCount) :
    cleared S (GaussPivotFraming32.locate j) = [] := by
  have h := GaussWorkerReset32.reset_empty S
    (⟨j.val, by
      have : (SourceListMachineWriter.framingMachine false).stackCount = 8 := rfl
      omega⟩ : Fin 8)
  simpa [cleared,GaussPivotFraming32.locate,
    GaussWorkerReset32.bank] using h

#print axioms reset_phase
#print axioms preserves
#print axioms worker_empty

end
end CurrentAdditive.GaussStepWriterResetRun32
