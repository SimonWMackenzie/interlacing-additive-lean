import CurrentAdditive.CodeDCanonicalSourceV2
import EthInapproximability.CurrentPaper.BankFieldProjection
import EthInapproximability.CurrentPaper.SourceListMachineOuterFramed

/-! The physical source scan removes only the rational weight from each
indexed entry. The ordered encoded tuples retain duplicate source indices. -/

namespace CurrentAdditive.CylinderSourceTupleProjection

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine

def inputItems {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) :
    List (List Bool) :=
  (CodeDCanonicalSourceV2.canonicalSource source).map
    CodeDSourceCodecV2.encodeEntry

def tupleWords {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) :
    List (List Bool) :=
  source.toList.map (fun x =>
    SourceListEncoding.encode (List.ofFn (fun j : Fin q => (x.1 j).bits)))

def projectTuple (item : List Bool) : List Bool :=
  BankFieldProjection.result (0 : Fin 2) item

noncomputable def projectMachine : Machine :=
  SourceListMachineOuterFramed.machine
    (BankFieldProjection.machine (0 : Fin 2))

noncomputable def projectClock {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) : Nat :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine
      (BankFieldProjection.machine (0 : Fin 2)))
    (inputItems source)
    (SourceListMachineOuterFramed.framedOutput projectTuple)
    (SourceListMachineOuterFramed.framedBound projectTuple
      (fun item => 8 * (item.length + 1)))

theorem projectTuple_entry (entry : CodeDSourceCodecV2.Entry) :
    projectTuple (CodeDSourceCodecV2.encodeEntry entry) =
      SourceListEncoding.encode entry.word := by
  simp [projectTuple, CodeDSourceCodecV2.encodeEntry,
    CodeDCodecV2.encodeItems]

theorem source_tuple_output {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) :
    projectMachine.OutputsWithin
      (CodeDCanonicalSourceV2.encodedSource source)
      (SourceListEncoding.encode (tupleWords source))
      (projectClock source) := by
  have hitem : ∀ item ∈ inputItems source,
      (BankFieldProjection.machine (0 : Fin 2)).OutputsWithin
        item (projectTuple item) (8 * (item.length + 1)) := by
    intro item _
    exact BankFieldProjection.outputs (0 : Fin 2) item
  have h := SourceListMachineOuterFramed.outputsWithin
    (BankFieldProjection.machine (0 : Fin 2)) (inputItems source)
    projectTuple (fun item => 8 * (item.length + 1)) hitem
  have hmap : (inputItems source).map projectTuple = tupleWords source := by
    simp [inputItems, tupleWords, CodeDCanonicalSourceV2.canonicalSource,
      List.map_map, projectTuple_entry, CodeDCanonicalSourceV2.canonicalEntry]
  rw [hmap] at h
  simpa only [projectMachine, projectClock,
    CodeDCanonicalSourceV2.encodedSource, CodeDSourceCodecV2.encodeSource,
    CodeDCodecV2.encodeItems, inputItems] using h

#print axioms source_tuple_output

end CurrentAdditive.CylinderSourceTupleProjection
