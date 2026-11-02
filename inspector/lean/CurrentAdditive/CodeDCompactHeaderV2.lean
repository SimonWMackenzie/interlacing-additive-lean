import CurrentAdditive.CodeDCompactBodyV2
import CurrentAdditive.CodeDKeepFlagV2
import CurrentAdditive.CodeDZeroListV2
import EthInapproximability.CurrentPaper.SourceListMachineWriter

/-!
The new list count is computed from the updated entries, never copied from
the old list header.  A physical zero-flag pass feeds a unary keep-count pass,
then a physical canonical count-field writer.
-/

namespace CurrentAdditive.CodeDCompactHeaderV2

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CodeDZeroCompactSpecV2

def flags (items : List (List Bool)) : List (List Bool) :=
  CodeDZeroListV2.flags items

def unary (items : List (List Bool)) : List Bool :=
  CodeDKeepFlagV2.output (flags items)

noncomputable def flagMachine : BitMachine.Machine :=
  BitMachineComposition.composition
    CodeDZeroListV2.machine CodeDKeepFlagV2.machine

noncomputable def flagClock (items : List (List Bool)) : Nat :=
  CodeDZeroListV2.clock items +
    2*(CodeDZeroListV2.output items).length+2 +
    CodeDKeepFlagV2.clock (flags items)

theorem flag_outputs (items : List (List Bool)) :
    flagMachine.OutputsWithin (CodeDCodecV2.encodeItems items)
      (unary items) (flagClock items) := by
  exact BitMachineComposition.composition_outputsWithin
    CodeDZeroListV2.machine CodeDKeepFlagV2.machine
    (CodeDZeroListV2.outputs items)
    (CodeDKeepFlagV2.outputs (flags items))

theorem unary_exact (items : List (List Bool)) :
    unary items = List.replicate (selectedBytes items).length true := by
  induction items with
  | nil => rfl
  | cons x xs ih =>
      change CodeDKeepFlagV2.result (CodeDZeroEntryV2.result x) ++ unary xs =
        List.replicate (selectedBytes (x :: xs)).length true
      rw [ih]
      rcases CodeDKeepEntryV2.zero_result_flag x with hz | hk
      · simp [CodeDKeepFlagV2.result, hz, selectedBytes, keepByte]
      · simp [CodeDKeepFlagV2.result, hk, selectedBytes, keepByte,
          List.replicate_succ]

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition flagMachine
    (SourceListMachineWriter.framingMachine false)

def output (items : List (List Bool)) : List Bool :=
  natField (selectedBytes items).length

noncomputable def clock (items : List (List Bool)) : Nat :=
  flagClock items + 2*(unary items).length+2 +
    (UnaryBinaryEncoding.coefficient+7)*
      ((unary items).length+1)^2

theorem outputs (items : List (List Bool)) :
    machine.OutputsWithin (CodeDCodecV2.encodeItems items)
      (output items) (clock items) := by
  have h := BitMachineComposition.composition_outputsWithin
    flagMachine (SourceListMachineWriter.framingMachine false)
    (flag_outputs items)
    (SourceListMachineWriter.outputs false (unary items))
  simpa only [machine, clock, output, SourceListMachineWriter.result,
    unary_exact, List.length_replicate, Bool.false_eq_true, ↓reduceIte,
    List.append_nil] using h

#print axioms unary_exact
#print axioms outputs

end CurrentAdditive.CodeDCompactHeaderV2
