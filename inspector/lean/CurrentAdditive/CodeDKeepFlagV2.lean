import CurrentAdditive.CodeDStripHeaderV2
import EthInapproximability.CurrentPaper.SourceListMachineOuterRun
import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
Physical unary keep-count pass over the controller's one-bit zero flags.
Each false flag contributes exactly one unary cell; true contributes none.
The inherited list iterator prepends its old count, which the separate
physical header-strip machine removes.
-/

namespace CurrentAdditive.CodeDKeepFlagV2

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

def program : Unit → TM2.Stmt (fun _ : Fin 2 => Bool) Unit (Option Bool)
  | () => pop 0 (fun _ b => b)
      (branch (fun b => b == some false)
        (push 1 (fun _ => true) halt) halt)

def result (input : List Bool) : List Bool :=
  if input.head? = some false then [true] else []

noncomputable def itemMachine : BitMachine.Machine :=
  ofFinite (0 : Fin 2) 1 () (none : Option Bool) program

theorem item_outputs (input : List Bool) :
    itemMachine.OutputsWithin input (result input) 1 := by
  apply outputsWithin_of_raw_run (0 : Fin 2) 1 ()
    (none : Option Bool) program input (result input) 1 1 le_rfl
  · cases input with
    | nil => rfl
    | cons b rest => cases b <;> rfl
  · cases input with
    | nil => rfl
    | cons b rest => cases b <;> rfl

noncomputable def markedMachine : BitMachine.Machine :=
  SourceListMachineOuter.machine itemMachine

def markedOutput (flags : List (List Bool)) : List Bool :=
  EthInapproximability.CurrentPaper.EncodedCommunication.natField flags.length ++
    SourceListMachineOuter.joined flags result

noncomputable def markedClock (flags : List (List Bool)) : Nat :=
  SourceListMachineOuter.canonicalBound itemMachine flags result (fun _ => 1)

theorem marked_outputs (flags : List (List Bool)) :
    markedMachine.OutputsWithin
      (SourceListEncoding.encode flags) (markedOutput flags)
      (markedClock flags) := by
  exact SourceListMachineOuter.canonical_outputsWithin itemMachine flags result
    (fun _ => 1) (by intro x _; exact item_outputs x)

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition markedMachine CodeDStripHeaderV2.machine

def output (flags : List (List Bool)) : List Bool :=
  SourceListMachineOuter.joined flags result

noncomputable def clock (flags : List (List Bool)) : Nat :=
  markedClock flags + 2*(markedOutput flags).length+2 +
    (2*(markedOutput flags).length+3)

theorem outputs (flags : List (List Bool)) :
    machine.OutputsWithin (SourceListEncoding.encode flags)
      (output flags) (clock flags) := by
  have h₁ := marked_outputs flags
  have h₂ := CodeDStripHeaderV2.outputs_valid flags.length (output flags)
  exact BitMachineComposition.composition_outputsWithin
    markedMachine CodeDStripHeaderV2.machine h₁ h₂

theorem output_one_bit_flags (flags : List Bool) :
    output (flags.map fun b => [b]) = List.replicate
      (flags.filter (fun b => !b)).length true := by
  induction flags with
  | nil => rfl
  | cons b bs ih =>
      have htail : SourceListMachineOuter.joined
          (bs.map fun b => [b]) result =
          List.replicate (bs.filter (fun b => !b)).length true := ih
      cases b <;>
        simp [output, SourceListMachineOuter.joined_cons,
          result, htail, List.filter_cons, List.replicate_succ]

#print axioms item_outputs
#print axioms marked_outputs
#print axioms outputs
#print axioms output_one_bit_flags

end CurrentAdditive.CodeDKeepFlagV2
