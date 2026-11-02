import CurrentAdditive.CodeDKeepEntryV2
import CurrentAdditive.CodeDZeroCompactSpecV2
import EthInapproximability.CurrentPaper.SourceListMachineOuterRun
import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
Physical body pass: visit every post-update entry in its original position,
write its complete length-prefixed bytes only when its numerator is nonzero,
and remove the iterator's old count.  The new count header is a separate pass.
-/

namespace CurrentAdditive.CodeDCompactBodyV2

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CodeDZeroCompactSpecV2

noncomputable def listMachine : BitMachine.Machine :=
  SourceListMachineOuter.machine CodeDKeepEntryV2.machine

def listOutput (items : List (List Bool)) : List Bool :=
  natField items.length ++
    SourceListMachineOuter.joined items CodeDKeepEntryV2.result

noncomputable def listClock (items : List (List Bool)) : Nat :=
  SourceListMachineOuter.canonicalBound CodeDKeepEntryV2.machine items
    CodeDKeepEntryV2.result CodeDKeepEntryV2.clock

theorem list_outputs (items : List (List Bool)) :
    listMachine.OutputsWithin (CodeDCodecV2.encodeItems items)
      (listOutput items) (listClock items) := by
  exact SourceListMachineOuter.canonical_outputsWithin
    CodeDKeepEntryV2.machine items CodeDKeepEntryV2.result
    CodeDKeepEntryV2.clock (by intro x _; exact CodeDKeepEntryV2.outputs x)

theorem item_result (x : List Bool) :
    CodeDKeepEntryV2.result x =
      if keepByte x then natField x.length ++ x else [] := by
  rcases CodeDKeepEntryV2.zero_result_flag x with hz | hk
  · simp [CodeDKeepEntryV2.result, keepByte, hz]
  · simp [CodeDKeepEntryV2.result, keepByte, hk,
      SourceListMachineWriter.result]

theorem joined_exact (items : List (List Bool)) :
    SourceListMachineOuter.joined items CodeDKeepEntryV2.result =
      SourceListEncoding.fields (selectedBytes items) := by
  induction items with
  | nil => rfl
  | cons x xs ih =>
      simp only [selectedBytes] at ih
      rw [SourceListMachineOuter.joined_cons, item_result]
      simp only [selectedBytes, List.filter_cons]
      cases h : keepByte x <;>
        simp [h, SourceListEncoding.fields, ih]

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition listMachine CodeDStripHeaderV2.machine

def output (items : List (List Bool)) : List Bool :=
  SourceListEncoding.fields (selectedBytes items)

noncomputable def clock (items : List (List Bool)) : Nat :=
  listClock items + 2*(listOutput items).length+2 +
    (2*(listOutput items).length+3)

theorem outputs (items : List (List Bool)) :
    machine.OutputsWithin (CodeDCodecV2.encodeItems items)
      (output items) (clock items) := by
  have h₁ := list_outputs items
  have h₂ := CodeDStripHeaderV2.outputs_valid items.length
    (output items)
  have hs : listOutput items = natField items.length ++ output items := by
    exact congrArg (natField items.length ++ ·) (joined_exact items)
  rw [← hs] at h₂
  exact BitMachineComposition.composition_outputsWithin
    listMachine CodeDStripHeaderV2.machine h₁ h₂

#print axioms list_outputs
#print axioms joined_exact
#print axioms outputs

end CurrentAdditive.CodeDCompactBodyV2
