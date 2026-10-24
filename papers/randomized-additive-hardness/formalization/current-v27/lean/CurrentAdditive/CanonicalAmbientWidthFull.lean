import CurrentAdditive.CanonicalAmbientSourceDegree

/-! Physical source H,K copies followed by the exact field-word width
multiplication as one ambient TM2 program. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.YaoMachine

def widthInputBank (t N H K : ℕ) (S : Cell t N → List Bool) :=
  Function.update
    (Function.update S (.width 0) (List.replicate H true))
    (.width 1) (List.replicate K true)

def widthFullProgram (t N : ℕ) :=
  BitMachineRawSequence.program (widthInputProgram t N) (widthStage t N)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (none, none) (none, ((), false))

theorem widthInputBank_local (t N H K : ℕ) (S : Cell t N → List Bool)
    (hblank : ∀ i : Fin 8, S (.width i) = [])
    (i : Fin 8) :
    widthInputBank t N H K S (.width i) =
      CanonicalWidthMultiply.initial H K i := by
  fin_cases i <;>
    simp_all [widthInputBank, CanonicalWidthMultiply.initial]

theorem physical_width_full (t N H K : ℕ) (S : Cell t N → List Bool)
    (hH : S (.source (sN 6)) = List.replicate H true)
    (hK : S (.source (sN 9)) = List.replicate K true)
    (hblank : ∀ i : Fin 8, S (.width i) = [])
    (hscratch : S (.copyScratch 0) = []) :
    ∃ steps ≤ ((2*H+2) + (2*K+2) + 1) +
        ((2*K+2) + 2 + MatrixAddressMachine.exactTime H (K+1) 0 + 2) + 1,
      ((advance (widthFullProgram t N))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          ((none, none), (none, ((), false))), S⟩ :
            TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
        ⟨none, ((none, none), (none, ((), false))),
          bank (widthEmbed t N) (widthInputBank t N H K S)
            (Function.update (Function.update
              (CanonicalWidthMultiply.initial H K) 2
              (List.replicate (K+1) true)) 3
              (List.replicate (H*(K+1)) true))⟩ := by
  let S1 := widthInputBank t N H K S
  obtain ⟨s, hs, hcopy⟩ := physical_width_inputs t N H K S
    hH hK (hblank 0) (hblank 1) hscratch
  obtain ⟨u, hu, hwidth⟩ := physical_ambient_width t N H K S1
    (widthInputBank_local t N H K S hblank)
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (widthInputProgram t N) (widthStage t N)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (none, none) (none, none)
    (none, ((), false)) (none, ((), false))
    S S1 _ s u (by simpa [S1, widthInputBank] using hcopy) hwidth
  exact ⟨steps, by omega,
    by simpa [widthFullProgram, S1, widthInputBank, stackCfg] using hrun⟩

#print axioms physical_width_full

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
