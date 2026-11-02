import CurrentAdditive.CanonicalFieldSquare

/-! One fixed three-stage TM2 program writes the exact canonical threshold
`2*b+4*t+2` from unary address width b. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalThreshold

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

def cp : Fin 3 ↪ Fin 3 := ⟨![0, 1, 2], by decide⟩
def fixed (t : ℕ) := SourceClauseFixedUnary.program (1 : Fin 3) (4*t+2)
def copyFixed (t : ℕ) := BitMachineRawSequence.program
  (MatrixStage4ScalarPreparationOps.copyProgram cp) (fixed t)
  (0 : SourceClauseFixedUnary.Label (4*t+2)) none ()
def program (t : ℕ) := BitMachineRawSequence.program
  (MatrixStage4ScalarPreparationOps.copyProgram cp) (copyFixed t)
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
  none (none, ())

def initial (b : ℕ) : Fin 3 → List Bool :=
  (![List.replicate b true, [], []] : Fin 3 → List Bool)

theorem physical_threshold (t b : ℕ) :
    ∃ steps ≤ 2*(2*b+2) + (4*t+3) + 2,
      ((advance (program t))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, (none, ())), initial b⟩ :
          TM2.Cfg (fun _ : Fin 3 => Bool) _ _) =
        ⟨none, (none, (none, ())),
          Function.update (initial b) 1
            (List.replicate (2*b+4*t+2) true)⟩ := by
  let S := initial b
  let S1 := Function.update S 1 (List.replicate b true)
  let S2 := Function.update S1 1 (List.replicate (2*b) true)
  let S3 := Function.update S2 1 (List.replicate (2*b+4*t+2) true)
  have h1 := MatrixStage4ScalarPreparationOps.copy_run cp S (by rfl)
  have h1' : ((advance (MatrixStage4ScalarPreparationOps.copyProgram cp))^[2*b+2])
      (⟨some BitMachineCopy.Label.scan, none, S⟩ :
        TM2.Cfg (fun _ : Fin 3 => Bool) _ _) = ⟨none, none, S1⟩ := by
    simpa [cp, S1, S, initial] using h1
  have h2 := MatrixStage4ScalarPreparationOps.copy_run cp S1
    (by simp [S1, S, initial, cp])
  have h2' : ((advance (MatrixStage4ScalarPreparationOps.copyProgram cp))^[2*b+2])
      (⟨some BitMachineCopy.Label.scan, none, S1⟩ :
        TM2.Cfg (fun _ : Fin 3 => Bool) _ _) = ⟨none, none, S2⟩ := by
    simpa [cp, S2, S1, S, initial, ← List.replicate_add, two_mul] using h2
  have h3 := SourceClauseFixedUnary.run_from (1 : Fin 3) S2
    (0 : SourceClauseFixedUnary.Label (4*t+2)) (4*t+2) (by simp)
    (List.replicate (2*b) true)
  have h3' : ((advance (fixed t))^[4*t+3])
      (⟨some (0 : SourceClauseFixedUnary.Label (4*t+2)), (), S2⟩ :
        TM2.Cfg (fun _ : Fin 3 => Bool) _ _) = ⟨none, (), S3⟩ := by
    have hclock : (4*t+2)+1 = 4*t+3 := by omega
    rw [← hclock]
    simpa [fixed, SourceClauseFixedUnary.state, S3, S2, S1, S, initial,
      ← List.replicate_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h3
  obtain ⟨u, hu, hr23⟩ := BitMachineRawSequence.runs
    (MatrixStage4ScalarPreparationOps.copyProgram cp) (fixed t)
    BitMachineCopy.Label.scan (0 : SourceClauseFixedUnary.Label (4*t+2))
    none none () () S1 S2 S3 (2*b+2) (4*t+3) h2' h3'
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (MatrixStage4ScalarPreparationOps.copyProgram cp) (copyFixed t)
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none (none, ()) (none, ()) S S1 S3 (2*b+2) u h1' hr23
  refine ⟨steps, by omega, ?_⟩
  have hbank : S3 = Function.update S 1
      (List.replicate (2*b+4*t+2) true) := by
    simp [S3, S2, S1, Function.update_idem]
  rw [hbank] at hrun
  simpa [program, S] using hrun

#print axioms physical_threshold

end CurrentAdditive.FiniteFieldConstructor.CanonicalThreshold
