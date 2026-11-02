import CurrentAdditive.CanonicalAmbientSourceWidthRun

/-! Physical handoff of the public unary degree and field-list width to the
combined field initialization/search/printer machine. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding

def fieldDegreePlace (t N : ℕ) (hN : 3 < N) : Fin 3 ↪ Cell t N :=
  ⟨![.degree ⟨3, hN⟩, .fieldInit 0, .copyScratch 0], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩

def fieldWidthPlace (t N : ℕ) : Fin 3 ↪ Cell t N :=
  ⟨![.width 3, .fieldInit 1, .copyScratch 0], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩

def fieldInputProgram (t N : ℕ) (hN : 3 < N) :=
  BitMachineRawSequence.program
    (MatrixStage4ScalarPreparationOps.copyProgram (fieldDegreePlace t N hN))
    (MatrixStage4ScalarPreparationOps.copyProgram (fieldWidthPlace t N))
    BitMachineCopy.Label.scan none none

theorem physical_field_inputs (t N d n : ℕ) (hN : 3 < N)
    (S : Cell t N → List Bool)
    (hd : S (.degree ⟨3, hN⟩) = List.replicate d true)
    (hn : S (.width 3) = List.replicate n true)
    (hfield0 : S (.fieldInit 0) = [])
    (hfield1 : S (.fieldInit 1) = [])
    (hscratch : S (.copyScratch 0) = []) :
    ∃ steps ≤ (2*d+2) + (2*n+2) + 1,
      ((advance (fieldInputProgram t N hN))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, none), S⟩ : TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
        ⟨none, (none, none),
          Function.update (Function.update S (.fieldInit 0)
            (List.replicate d true)) (.fieldInit 1)
            (List.replicate n true)⟩ := by
  let S1 := Function.update S (.fieldInit 0) (List.replicate d true)
  let S2 := Function.update S1 (.fieldInit 1) (List.replicate n true)
  have hr1 := MatrixStage4ScalarPreparationOps.copy_run (fieldDegreePlace t N hN) S hscratch
  have hr1' : ((advance (MatrixStage4ScalarPreparationOps.copyProgram (fieldDegreePlace t N hN)))^[2*d+2])
      (⟨some BitMachineCopy.Label.scan, none, S⟩ : TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
      ⟨none, none, S1⟩ := by
    simpa [fieldDegreePlace, S1, hd, hfield0] using hr1
  have hr2 := MatrixStage4ScalarPreparationOps.copy_run (fieldWidthPlace t N) S1
    (by simp [fieldWidthPlace, S1, hscratch])
  have hr2' : ((advance (MatrixStage4ScalarPreparationOps.copyProgram (fieldWidthPlace t N)))^[2*n+2])
      (⟨some BitMachineCopy.Label.scan, none, S1⟩ : TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
      ⟨none, none, S2⟩ := by
    simpa [fieldWidthPlace, S2, S1, hn, hfield1] using hr2
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (MatrixStage4ScalarPreparationOps.copyProgram (fieldDegreePlace t N hN))
    (MatrixStage4ScalarPreparationOps.copyProgram (fieldWidthPlace t N))
    BitMachineCopy.Label.scan BitMachineCopy.Label.scan
    none none none none S S1 S2 (2*d+2) (2*n+2) hr1' hr2'
  exact ⟨steps, by omega, by simpa [fieldInputProgram, S2, S1] using hrun⟩

#print axioms physical_field_inputs

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
