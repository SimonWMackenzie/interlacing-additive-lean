import Paper2.Y0EntryEmbedding

/-! One fixed raw program first copies the literal input tape into the flat
source bank, then executes the frozen scalar loader. The raw-sequence
handoff costs one transition and resets the finite control. -/

namespace Paper2.YaoEntryControllerJoin

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineComposition
open EthInapproximability.CurrentPaper.BitMachineSubroutine
open Paper2.YaoEntryParameterJoin
open Paper2.YaoParameterBank

abbrev LoaderLabel (t lambda : ℕ) :=
  BitMachineRawSequence.Label (LiftScalarLabel t lambda) RouteLabel
abbrev LoaderControl (t lambda : ℕ) := LiftScalarControl t lambda × Option Bool
abbrev LiftLoaderLabel (t lambda : ℕ) := LoaderLabel t lambda ⊕ Unit
abbrev LiftLoaderControl (t lambda : ℕ) := LoaderControl t lambda × Unit

noncomputable def loaderStart (t lambda : ℕ) : LoaderLabel t lambda :=
  .inl (.inl (.inl (.inl (.inl (.inl (widthStartLabel t lambda))))))

noncomputable def loaderInitialControl (t lambda : ℕ) :
    LoaderControl t lambda :=
  ((((fixedSelectorControl t lambda,()),false),()),none)

noncomputable def liftLoaderProgram (t lambda : ℕ) :
    LiftLoaderLabel t lambda →
      TM2.Stmt (fun _ : InputStack t lambda => Bool)
        (LiftLoaderLabel t lambda) (LiftLoaderControl t lambda)
  | .inl l => liftStmt none (routedParameterProgram t lambda
      (fixedStageControl t lambda) (fixedSelectorControl t lambda) l)
  | .inr () => .halt

noncomputable def loadedParameterProgram (t lambda : ℕ) :=
  BitMachineRawSequence.program
    (tapeCopyProgram t lambda) (liftLoaderProgram t lambda)
    (.inl (loaderStart t lambda)) none
    (loaderInitialControl t lambda,())

theorem loaded_parameters_from_run (t lambda : ℕ)
    (S₀ : PayloadStack t lambda → List Bool)
    (R : RouteStack t lambda → List Bool)
    (source : List Bool) (loaderSteps : ℕ)
    (hrun : ((advance (routedParameterProgram t lambda
        (fixedStageControl t lambda) (fixedSelectorControl t lambda)))^[loaderSteps])
      (⟨some (loaderStart t lambda),loaderInitialControl t lambda,
        Sum.elim S₀ (routedForeign source)⟩ :
        TM2.Cfg (fun _ : RouteStack t lambda => Bool)
          (LoaderLabel t lambda) (LoaderControl t lambda)) =
      ⟨none,loaderInitialControl t lambda,R⟩) :
    ∃ (copySteps total : ℕ),
      copySteps ≤ 2*source.length+2 ∧
      total ≤ copySteps+loaderSteps+1 ∧
      ((advance (loadedParameterProgram t lambda))^[total])
        (⟨some (.inl .scan),
          (none,(loaderInitialControl t lambda,())),
          tapeRawBank S₀ source⟩ :
          TM2.Cfg (fun _ : InputStack t lambda => Bool) _ _) =
        ⟨none,(none,(loaderInitialControl t lambda,())),
          Sum.elim R (fun _ => source)⟩ := by
  let c : TM2.Cfg (fun _ : RouteStack t lambda => Bool)
      (LoaderLabel t lambda) (LoaderControl t lambda) :=
    ⟨some (loaderStart t lambda),loaderInitialControl t lambda,
      Sum.elim S₀ (routedForeign source)⟩
  have hhalt : (((advance (routedParameterProgram t lambda
      (fixedStageControl t lambda) (fixedSelectorControl t lambda)))^[loaderSteps]) c).l =
      none := by rw [hrun]
  obtain ⟨liftSteps,hlift,hLift⟩ := lift_outputs
    (routedParameterProgram t lambda
      (fixedStageControl t lambda) (fixedSelectorControl t lambda))
    (liftLoaderProgram t lambda) none (by intro l; rfl)
    () (fun _ => source) c loaderSteps hhalt
  have hLift' : ((advance (liftLoaderProgram t lambda))^[liftSteps])
      (⟨some (.inl (loaderStart t lambda)),
        (loaderInitialControl t lambda,()),tapeLoadedBank S₀ source⟩ :
        TM2.Cfg (fun _ : InputStack t lambda => Bool)
          (LiftLoaderLabel t lambda) (LiftLoaderControl t lambda)) =
      ⟨none,(loaderInitialControl t lambda,()),Sum.elim R (fun _ => source)⟩ := by
    rw [hrun] at hLift
    simpa only [liftCfg,c,tapeLoadedBank,Option.map_none] using hLift
  obtain ⟨copySteps,hcopy,hCopy⟩ :=
    ExactParameterBranchInstall.copy_run (tapeCopyEmbed t lambda)
      (tapeRawBank S₀ source) source
      (tape_raw_source t lambda S₀ source)
      (tape_raw_target t lambda S₀ source)
      (tape_raw_scratch t lambda S₀ source)
  have hCopy' : ((advance (tapeCopyProgram t lambda))^[copySteps])
      (⟨some .scan,none,tapeRawBank S₀ source⟩ :
        TM2.Cfg (fun _ : InputStack t lambda => Bool)
          BitMachineCopy.Label (Option Bool)) =
      ⟨none,none,tapeLoadedBank S₀ source⟩ := by
    have hCopy' := hCopy
    change ((advance (tapeCopyProgram t lambda))^[copySteps])
      (⟨some .scan,none,tapeRawBank S₀ source⟩ :
        TM2.Cfg (fun _ : InputStack t lambda => Bool)
          BitMachineCopy.Label (Option Bool)) =
      ⟨none,none,Function.update (tapeRawBank S₀ source)
        (tapeTarget t lambda) source⟩ at hCopy'
    rw [tape_loaded_eq_update] at hCopy'
    exact hCopy'
  obtain ⟨total,htotal,hjoined⟩ := BitMachineRawSequence.runs
    (tapeCopyProgram t lambda) (liftLoaderProgram t lambda)
    .scan (.inl (loaderStart t lambda)) none none
    (loaderInitialControl t lambda,()) (loaderInitialControl t lambda,())
    (tapeRawBank S₀ source) (tapeLoadedBank S₀ source)
    (Sum.elim R (fun _ => source)) copySteps liftSteps hCopy' hLift'
  refine ⟨copySteps,total,hcopy,by omega,?_⟩
  simpa only [loadedParameterProgram,BitMachineRawSequence.leftLabel] using hjoined

#print axioms loaded_parameters_from_run

end Paper2.YaoEntryControllerJoin
