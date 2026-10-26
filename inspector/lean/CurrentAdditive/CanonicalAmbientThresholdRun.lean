import CurrentAdditive.CanonicalAmbientDimensionsRun

/-! The source address width is physically copied to the threshold input;
the exact threshold program then runs on the shared ambient stack namespace. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.YaoMachine

def thresholdBPlace (t N : ℕ) : Fin 3 ↪ Cell t N :=
  ⟨![.source (sN 5), .threshold 0, .copyScratch 0], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩

theorem physical_threshold_input (t N b : ℕ) (S : Cell t N → List Bool)
    (hb : S (.source (sN 5)) = List.replicate b true)
    (hthreshold : S (.threshold 0) = [])
    (hscratch : S (.copyScratch 0) = []) :
    ((advance (MatrixStage4ScalarPreparationOps.copyProgram
      (thresholdBPlace t N)))^[2*b+2])
      (⟨some BitMachineCopy.Label.scan, none, S⟩ :
        TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
      ⟨none, none,
        Function.update S (.threshold 0) (List.replicate b true)⟩ := by
  have hr := MatrixStage4ScalarPreparationOps.copy_run
    (thresholdBPlace t N) S (by simpa [thresholdBPlace] using hscratch)
  simpa [thresholdBPlace, hb, hthreshold] using hr

def thresholdStage (t N : ℕ) :=
  fun l => stackStmt (thresholdEmbed t N)
    (CanonicalThreshold.program t l)

theorem physical_ambient_threshold (t N b : ℕ) (S : Cell t N → List Bool)
    (hlocal : ∀ i : Fin 3,
      S (.threshold i) = CanonicalThreshold.initial b i) :
    ∃ steps ≤ 2*(2*b+2) + (4*t+3) + 2,
      ((advance (thresholdStage t N))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, (none, ())), S⟩ :
            TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
        stackCfg (thresholdEmbed t N) S
          (⟨none, (none, (none, ())),
            Function.update (CanonicalThreshold.initial b) 1
              (List.replicate (2*b+4*t+2) true)⟩ :
                TM2.Cfg (fun _ : Fin 3 => Bool) _ _) := by
  obtain ⟨steps, hsteps, hrun⟩ :=
    CanonicalThreshold.physical_threshold t b
  refine ⟨steps, hsteps, ?_⟩
  have hbank := bank_eq_self (thresholdEmbed t N) S _
    (by intro i; exact (hlocal i).symm)
  have he := EthInapproximability.CurrentPaper.BitMachineStackRun.run
    (thresholdEmbed t N) S (CanonicalThreshold.program t)
    (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
      (none, (none, ())), CanonicalThreshold.initial b⟩ :
        TM2.Cfg (fun _ : Fin 3 => Bool) _ _) steps
  have hr := congrArg (stackCfg (thresholdEmbed t N) S) hrun
  have hcombined := he.trans hr
  simpa [thresholdStage, stackCfg, hbank] using hcombined

#print axioms physical_threshold_input
#print axioms physical_ambient_threshold

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
