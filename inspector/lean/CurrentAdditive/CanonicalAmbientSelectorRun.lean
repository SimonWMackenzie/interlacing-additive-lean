import CurrentAdditive.CanonicalAmbientHeaderRun

/-! The source H word is physically copied to the selector-power input, then
the fixed unary power program runs in the common ambient namespace. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.YaoMachine

def selectorHPlace (t N : ℕ) : Fin 3 ↪ Cell t N :=
  ⟨![.source (sN 6), .selector 6, .copyScratch 0], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩

theorem physical_selector_input (t N H : ℕ) (S : Cell t N → List Bool)
    (hH : S (.source (sN 6)) = List.replicate H true)
    (hselector : S (.selector 6) = [])
    (hscratch : S (.copyScratch 0) = []) :
    ((advance (MatrixStage4ScalarPreparationOps.copyProgram
      (selectorHPlace t N)))^[2*H+2])
      (⟨some BitMachineCopy.Label.scan, none, S⟩ :
        TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
      ⟨none, none,
        Function.update S (.selector 6) (List.replicate H true)⟩ := by
  have hr := MatrixStage4ScalarPreparationOps.copy_run
    (selectorHPlace t N) S (by simpa [selectorHPlace] using hscratch)
  simpa [selectorHPlace, hH, hselector] using hr

def selectorStage (t N : ℕ) :=
  fun l => stackStmt (selectorEmbed t N)
    (CanonicalSelectorBankPower.program t l)

theorem physical_ambient_selector (t N H : ℕ) (S : Cell t N → List Bool)
    (hlocal : ∀ i : Fin 12,
      S (.selector i) = CanonicalSelectorBankPower.initial H i) :
    ∃ steps ≤ (2 ^ (t - 1) + 1) +
        (MatrixWeightedPower.powerBound H (2 ^ (t - 1)) + 2) + 1,
      ((advance (selectorStage t N))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel
            (0 : SourceClauseFixedUnary.Label (2 ^ (t - 1)))),
          ((), (none, (false, false))), S⟩ :
            TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
        stackCfg (selectorEmbed t N) S
          (⟨none, ((), (none, (false, false))),
            Function.update (CanonicalSelectorBankPower.initial H) 1
              (List.replicate (H ^ (2 ^ (t - 1))) true)⟩ :
                TM2.Cfg (fun _ : Fin 12 => Bool) _ _) := by
  obtain ⟨steps, hsteps, hrun⟩ :=
    CanonicalSelectorBankPower.physical_selector_bank_power t H
  refine ⟨steps, hsteps, ?_⟩
  have hbank := bank_eq_self (selectorEmbed t N) S _
    (by intro i; exact (hlocal i).symm)
  have he := EthInapproximability.CurrentPaper.BitMachineStackRun.run
    (selectorEmbed t N) S (CanonicalSelectorBankPower.program t)
    (⟨some (BitMachineRawSequence.leftLabel
        (0 : SourceClauseFixedUnary.Label (2 ^ (t - 1)))),
      ((), (none, (false, false))),
      CanonicalSelectorBankPower.initial H⟩ :
        TM2.Cfg (fun _ : Fin 12 => Bool) _ _) steps
  have hr := congrArg (stackCfg (selectorEmbed t N) S) hrun
  have hcombined := he.trans hr
  simpa [selectorStage, stackCfg, hbank] using hcombined

#print axioms physical_selector_input
#print axioms physical_ambient_selector

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
