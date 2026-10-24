import Paper2.CodeRecursiveInitialLayout

/-! Physical composition of the actual successor compiler with its charged
bank reentry. This is one reusable round, not an uncharged recursive call. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.CodeRecursiveRound

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSource
open Paper2.CodeRecursiveColumn Paper2.CodeRecursiveRow
open Paper2.CodeRecursiveStep
open Paper2.CodeRecursiveReentry
open Paper2.CodeRecursiveInitialLayout

abbrev StepLabel1 := BitMachineRawSequence.Label ColLabel CodeRawCountTerm.Label
abbrev StepLabel2 := BitMachineRawSequence.Label StepLabel1 CodeRawCountTerm.Label
abbrev StepLabel3 := BitMachineRawSequence.Label StepLabel2 CodeRawCountTerm.Label
abbrev StepLabel4 := BitMachineRawSequence.Label StepLabel3 TaggedCompiler.Label
abbrev StepLabel5 := BitMachineRawSequence.Label StepLabel4 CodeAtomCountInput.Label
abbrev StepLabel6 := BitMachineRawSequence.Label StepLabel5 CodeConstructorMachine.Label
abbrev StepLabel := BitMachineRawSequence.Label StepLabel6 CodeCopiesMachine.Label

abbrev StepControl :=
  ((((((ColControl × TermControl) × TermControl) × TermControl) ×
    TaggedCompiler.Control) × CodeAtomCountInput.Control) ×
    CodeConstructorMachine.Control) × CodeCopiesMachine.Control

def stepStart : StepLabel :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel colStart))))))

def stepControl : StepControl :=
  (((((((colControl,termControl),termControl),termControl),none),
    ticketControl),none),none)

abbrev ReentryLabel1 := BitMachineRawSequence.Label
  (SourceClauseClearExcept.Label
    (SourceClauseClearExcept.workCount keepBefore)) BitMachineCopy.Label
abbrev ReentryLabel2 := BitMachineRawSequence.Label ReentryLabel1
  BitMachineCopy.Label
abbrev ReentryLabel := BitMachineRawSequence.Label ReentryLabel2
  (SourceClauseClearExcept.Label
    (SourceClauseClearExcept.workCount keepAfter))
abbrev ReentryControl :=
  (((Unit × Option Bool) × Option Bool) × Option Bool) ×
    (Unit × Option Bool)

def reentryStart : ReentryLabel :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (SourceClauseClearExcept.Label.clear 0)))

def reentryControl : ReentryControl := (((((),none),none),none),((),none))

noncomputable def program := BitMachineRawSequence.program
  CodeRecursiveStep.program CodeRecursiveReentry.program
  reentryStart stepControl reentryControl

noncomputable def clock (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) : Nat :=
  CodeRecursiveStep.clockBound n s q₁ q₂ w Q previousRow previousCol +
    CodeRecursiveReentry.clock
      (afterRow n s q₁ q₂ w Q previousRow previousCol) + 1

theorem run_exact (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (hs : 3 ≤ s) :
    ∃ t ≤ clock n s q₁ q₂ w Q previousRow previousCol,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel stepStart),
          (stepControl,reentryControl),
          initial n s q₁ q₂ w Q previousRow previousCol⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (stepControl,reentryControl),
          initial n s q₁ q₂ w Q
            (rowCode q₁ q₂ s w Q previousCol)
            (columnCode n s q₁ q₂ w Q previousRow)⟩ := by
  obtain ⟨ta,hta,ha⟩ := CodeRecursiveStep.run_exact
    n s q₁ q₂ w Q previousRow previousCol hs
  obtain ⟨tb,htb,hb⟩ := CodeRecursiveReentry.run_exact
    (afterRow n s q₁ q₂ w Q previousRow previousCol)
  rw [reentered_is_initial n s q₁ q₂ w Q
    previousRow previousCol] at hb
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    CodeRecursiveStep.program CodeRecursiveReentry.program
    stepStart reentryStart
    stepControl stepControl reentryControl reentryControl
    (initial n s q₁ q₂ w Q previousRow previousCol)
    (afterRow n s q₁ q₂ w Q previousRow previousCol)
    (initial n s q₁ q₂ w Q
      (rowCode q₁ q₂ s w Q previousCol)
      (columnCode n s q₁ q₂ w Q previousRow))
    ta tb ha hb
  exact ⟨t, by dsimp [clock]; omega, hr⟩

#print axioms run_exact

end Paper2.CodeRecursiveRound
