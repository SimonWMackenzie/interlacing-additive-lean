import CurrentAdditive.CanonicalAmbientSquareFull

/-! Physical source-b copy followed by the exact canonical threshold writer
as one ambient TM2 program. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.YaoMachine

def thresholdInputBank (t N b : ℕ) (S : Cell t N → List Bool) :=
  Function.update S (.threshold 0) (List.replicate b true)

def thresholdFullProgram (t N : ℕ) :=
  BitMachineRawSequence.program
    (MatrixStage4ScalarPreparationOps.copyProgram (thresholdBPlace t N))
    (thresholdStage t N)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none (none, (none, ()))

theorem thresholdInputBank_local (t N b : ℕ) (S : Cell t N → List Bool)
    (hblank : ∀ i : Fin 3, S (.threshold i) = [])
    (i : Fin 3) :
    thresholdInputBank t N b S (.threshold i) =
      CanonicalThreshold.initial b i := by
  fin_cases i <;>
    simp_all [thresholdInputBank, CanonicalThreshold.initial]

theorem physical_threshold_full (t N b : ℕ) (S : Cell t N → List Bool)
    (hb : S (.source (sN 5)) = List.replicate b true)
    (hblank : ∀ i : Fin 3, S (.threshold i) = [])
    (hscratch : S (.copyScratch 0) = []) :
    ∃ steps ≤ (2*b+2) + (2*(2*b+2) + (4*t+3) + 2) + 1,
      ((advance (thresholdFullProgram t N))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, (none, (none, ()))), S⟩ :
            TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
        ⟨none, (none, (none, (none, ()))),
          bank (thresholdEmbed t N) (thresholdInputBank t N b S)
            (Function.update (CanonicalThreshold.initial b) 1
              (List.replicate (2*b+4*t+2) true))⟩ := by
  let S1 := thresholdInputBank t N b S
  have hcopy := physical_threshold_input t N b S hb (hblank 0) hscratch
  obtain ⟨u, hu, hthreshold⟩ := physical_ambient_threshold t N b S1
    (thresholdInputBank_local t N b S hblank)
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (MatrixStage4ScalarPreparationOps.copyProgram (thresholdBPlace t N))
    (thresholdStage t N)
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none (none, (none, ()))
    (none, (none, ()))
    S S1 _ (2*b+2) u
    (by simpa [S1, thresholdInputBank] using hcopy) hthreshold
  exact ⟨steps, by omega,
    by simpa [thresholdFullProgram, S1, thresholdInputBank, stackCfg] using hrun⟩

#print axioms physical_threshold_full

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
