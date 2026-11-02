import CurrentAdditive.CodeDUpdatedEntryJoin
import CurrentAdditive.CodeDCompactSequentialBridge
import EthInapproximability.CurrentPaper.SourceListMachineOuterFramed

/-!
An ordered counted-list writer for updated entries. Each input item is a
packed pair of the old canonical Entry and the newly canonical RawRat weight.
The callback extracts the old word and physically writes the replacement
Entry. The list iterator frames each result and writes the new count.
-/

namespace CurrentAdditive.CodeDUpdatedEntryList

open EthInapproximability.CurrentPaper
open CodeDSourceCodecV2 CodeDCanonicalSourceV2

noncomputable def machine : BitMachine.Machine :=
  SourceListMachineOuterFramed.machine CodeDUpdatedEntryJoin.machine

def result (pairs : List (List Bool)) : List Bool :=
  CodeDCodecV2.encodeItems (pairs.map CodeDUpdatedEntryJoin.output)

noncomputable def clock (pairs : List (List Bool)) : Nat :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine CodeDUpdatedEntryJoin.machine)
    pairs
    (SourceListMachineOuterFramed.framedOutput CodeDUpdatedEntryJoin.output)
    (SourceListMachineOuterFramed.framedBound
      CodeDUpdatedEntryJoin.output CodeDUpdatedEntryJoin.clock)

theorem outputs (pairs : List (List Bool)) :
    machine.OutputsWithin (CodeDCodecV2.encodeItems pairs)
      (result pairs) (clock pairs) := by
  have h := SourceListMachineOuterFramed.outputsWithin
    CodeDUpdatedEntryJoin.machine pairs CodeDUpdatedEntryJoin.output
    CodeDUpdatedEntryJoin.clock
    (by intro x _; exact CodeDUpdatedEntryJoin.outputs x)
  simpa only [machine, result, clock, CodeDCodecV2.encodeItems] using h

def pairItems {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (updated : Array ℚ) :
    List (List Bool) :=
  (List.range updated.size).filterMap (fun i =>
    (source[i]?).map (fun old =>
      CodeDUpdatedEntryFields.pairPacket
        (canonicalEntry old) (updated[i]?.getD 0)))

theorem pairItems_map_exact {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (updated : Array ℚ) :
    (pairItems source updated).map CodeDUpdatedEntryJoin.output =
      (CodeDCompactSequentialBridge.updatedEntries source updated).map
        encodeEntry := by
  unfold pairItems CodeDCompactSequentialBridge.updatedEntries
    CodeDCompactSequentialBridge.updatedAt
  simp only [List.map_filterMap]
  apply List.filterMap_congr
  intro i hi
  cases hs : source[i]? with
  | none => simp [hs]
  | some old =>
      simp [hs, CodeDUpdatedEntryJoin.output,
        CodeDUpdatedEntryFields.fields_pair,
        CodeDCanonicalSourceV2.canonicalEntry]

theorem pairItems_result_exact {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (updated : Array ℚ) :
    result (pairItems source updated) =
      CodeDCodecV2.encodeItems
        ((CodeDCompactSequentialBridge.updatedEntries source updated).map
          encodeEntry) := by
  simp only [result, pairItems_map_exact]

theorem writes_compactor_input {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (updated : Array ℚ) :
    machine.OutputsWithin
      (CodeDCodecV2.encodeItems (pairItems source updated))
      (CodeDCodecV2.encodeItems
        ((CodeDCompactSequentialBridge.updatedEntries source updated).map
          encodeEntry))
      (clock (pairItems source updated)) := by
  have h := outputs (pairItems source updated)
  rw [pairItems_result_exact] at h
  exact h

#print axioms outputs
#print axioms pairItems_map_exact
#print axioms pairItems_result_exact
#print axioms writes_compactor_input

end CurrentAdditive.CodeDUpdatedEntryList
