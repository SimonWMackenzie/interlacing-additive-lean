import EthInapproximability.CurrentPaper.SourceClausePairOrdinalReset
import EthInapproximability.CurrentPaper.SourceClausePairOneSource
import EthInapproximability.CurrentPaper.SourceClausePairGateCycle

/-! Reusable fixed-control raw-sequence composition on the exact pair bank. -/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairMachineComposition

open Turing BitMachineEncoding
open scoped Classical

abbrev Stack := PairUnitLift.Stack

structure Routine where
  Label : Type
  Control : Type
  program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  start : Label
  initial : Control

def fromProgram {L V : Type}
    (P : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (start : L) (initial : V) : Routine :=
  ⟨L, V, P, start, initial⟩

def Runs (R : Routine) (S T : Stack → List Bool) (bound : Nat) : Prop :=
  ∃ time ≤ bound,
    ((advance R.program)^[time])
      (⟨some R.start, R.initial, S⟩ : TM2.Cfg (fun _ : Stack => Bool) R.Label R.Control) =
      ⟨none, R.initial, T⟩

noncomputable def sequence (A B : Routine) : Routine where
  Label := BitMachineRawSequence.Label A.Label B.Label
  Control := BitMachineRawSequence.Control A.Control B.Control
  program := BitMachineRawSequence.program A.program B.program B.start A.initial B.initial
  start := BitMachineRawSequence.leftLabel A.start
  initial := (A.initial, B.initial)

theorem runs_sequence (A B : Routine) (S T U : Stack → List Bool)
    (a b : Nat) (hA : Runs A S T a) (hB : Runs B T U b) :
    Runs (sequence A B) S U (a+b+1) := by
  obtain ⟨ta, hta, ha⟩ := hA
  obtain ⟨tb, htb, hb⟩ := hB
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs
    A.program B.program A.start B.start
    A.initial A.initial B.initial B.initial S T U ta tb ha hb
  exact ⟨t, by omega, h⟩

noncomputable def loader (s t : Fin 2) : Routine where
  Label := PairOrdinalLoader.Label
  Control := Option Bool
  program := PairOrdinalLoader.program s t
  start := .vertexCopy
  initial := none

noncomputable def reset : Routine where
  Label := PairOrdinalReset.Label
  Control := Option Bool
  program := PairOrdinalReset.program
  start := .drain
  initial := none

noncomputable def unit (w ell : Nat) (sign : Bool) : Routine :=
  fromProgram (PairUnitLift.unitProgram w ell sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (SourceClauseFixedBatch.labelAt
          (PrefixUnitClean.constantSize w ell) 0)))
    (((), PrefixUnitRun.startControl), ((), none))

noncomputable def gate (bit ell : Fin 2) (sign : Bool) (w : Nat) : Routine :=
  fromProgram (PairGateCycle.program bit ell sign w)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (SourceClauseFixedBatch.labelAt
                  (PrefixGateOperands.constantSize bit.val w) 0)))))))
    (((((((), ((), none)), ((), none)), none), ()),
      PairGateExecute.gateControl), ((), none))

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairMachineComposition
