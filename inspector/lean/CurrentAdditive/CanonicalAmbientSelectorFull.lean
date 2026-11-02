import CurrentAdditive.CanonicalAmbientHeaderTransfer

/-! Physical source-H copy followed by selector-capacity powering as one
literal ambient TM2 program. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.YaoMachine

def selectorInputBank (t N H : ℕ) (S : Cell t N → List Bool) :=
  Function.update S (.selector 6) (List.replicate H true)

def selectorFullProgram (t N : ℕ) :=
  BitMachineRawSequence.program
    (MatrixStage4ScalarPreparationOps.copyProgram (selectorHPlace t N))
    (selectorStage t N)
    (BitMachineRawSequence.leftLabel
      (0 : SourceClauseFixedUnary.Label (2 ^ (t - 1))))
    none ((), (none, (false, false)))

theorem selectorInputBank_local (t N H : ℕ) (S : Cell t N → List Bool)
    (hblank : ∀ i : Fin 12, S (.selector i) = [])
    (i : Fin 12) :
    selectorInputBank t N H S (.selector i) =
      CanonicalSelectorBankPower.initial H i := by
  fin_cases i <;>
    simp_all [selectorInputBank, CanonicalSelectorBankPower.initial]

theorem physical_selector_full (t N H : ℕ) (S : Cell t N → List Bool)
    (hH : S (.source (sN 6)) = List.replicate H true)
    (hblank : ∀ i : Fin 12, S (.selector i) = [])
    (hscratch : S (.copyScratch 0) = []) :
    ∃ steps ≤ (2*H+2) +
        ((2 ^ (t - 1) + 1) +
          (MatrixWeightedPower.powerBound H (2 ^ (t - 1)) + 2) + 1) + 1,
      ((advance (selectorFullProgram t N))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, ((), (none, (false, false)))), S⟩ :
            TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
        ⟨none, (none, ((), (none, (false, false)))),
          bank (selectorEmbed t N) (selectorInputBank t N H S)
            (Function.update (CanonicalSelectorBankPower.initial H) 1
              (List.replicate (H ^ (2 ^ (t - 1))) true))⟩ := by
  let S1 := selectorInputBank t N H S
  have hcopy := physical_selector_input t N H S hH (hblank 6) hscratch
  obtain ⟨u, hu, hpower⟩ := physical_ambient_selector t N H S1
    (selectorInputBank_local t N H S hblank)
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (MatrixStage4ScalarPreparationOps.copyProgram (selectorHPlace t N))
    (selectorStage t N)
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel
      (0 : SourceClauseFixedUnary.Label (2 ^ (t - 1))))
    none none ((), (none, (false, false)))
    ((), (none, (false, false)))
    S S1 _ (2*H+2) u
    (by simpa [S1, selectorInputBank] using hcopy) hpower
  exact ⟨steps, by omega,
    by simpa [selectorFullProgram, S1, selectorInputBank, stackCfg] using hrun⟩

#print axioms physical_selector_full

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
