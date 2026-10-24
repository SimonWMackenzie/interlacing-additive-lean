import CurrentAdditive.NextSourceDimensionsBridge

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec

def sourceThresholdOutput {t : ℕ} (x : YaoSource t) (u : ℕ) :
    Cell t 16 → List Bool :=
  let b := paddedEdgeBits x.2.1
  bank (thresholdEmbed t 16)
    (thresholdInputBank t 16 b (sourceDimensionsOutput x u))
    (Function.update (CanonicalThreshold.initial b) 1
      (List.replicate (2*b+4*t+2) true))

theorem physical_threshold_after_dimensions (t : ℕ)
    (x : YaoSource t) (u : ℕ) :
    let b := paddedEdgeBits x.2.1
    ∃ steps ≤ (2*b+2) + (2*(2*b+2)+(4*t+3)+2)+1,
      ((advance (thresholdFullProgram t 16))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, (none, (none, ()))),
          sourceDimensionsOutput x u⟩ :
            TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
        ⟨none, (none, (none, (none, ()))),
          sourceThresholdOutput x u⟩ := by
  dsimp only
  obtain ⟨hb, hblank, hscratch⟩ :=
    sourceDimensionsOutput_threshold_input x u
  obtain ⟨steps, hsteps, hrun⟩ := physical_threshold_full
    t 16 (paddedEdgeBits x.2.1) (sourceDimensionsOutput x u)
      hb hblank hscratch
  exact ⟨steps, hsteps,
    by simpa [sourceThresholdOutput] using hrun⟩

#print axioms physical_threshold_after_dimensions

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
