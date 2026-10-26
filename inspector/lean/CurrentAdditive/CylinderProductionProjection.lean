import CurrentAdditive.CodeDCanonicalSourceV2
import CurrentAdditive.CodeDTargetV2
import EthInapproximability.CurrentPaper.BankFieldProjection
import EthInapproximability.CurrentPaper.SourceListMachineOuterFramed

/-!
Physical projections from the production V2 packets actually used by Code D.
They preserve indexed order and repeated labels/tuples.  No generated feature
list is accepted as input here.
-/

namespace CurrentAdditive.CylinderProductionProjection

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine

def sourceItems {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) :
    List (List Bool) :=
  (CodeDCanonicalSourceV2.canonicalSource source).map
    CodeDSourceCodecV2.encodeEntry

def tupleWords {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) :
    List (List Bool) :=
  source.toList.map (fun entry =>
    SourceListEncoding.encode
      (List.ofFn (fun j : Fin q => (entry.1 j).bits)))

def projectWord (item : List Bool) : List Bool :=
  BankFieldProjection.result (0 : Fin 2) item

noncomputable def tupleMachine : Machine :=
  SourceListMachineOuterFramed.machine
    (BankFieldProjection.machine (0 : Fin 2))

noncomputable def tupleClock {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) : Nat :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine
      (BankFieldProjection.machine (0 : Fin 2)))
    (sourceItems source)
    (SourceListMachineOuterFramed.framedOutput projectWord)
    (SourceListMachineOuterFramed.framedBound projectWord
      (fun item => 8 * (item.length + 1)))

theorem project_source_tuple {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) :
    tupleMachine.OutputsWithin
      (CodeDCanonicalSourceV2.encodedSource source)
      (SourceListEncoding.encode (tupleWords source))
      (tupleClock source) := by
  have hitem : ∀ item ∈ sourceItems source,
      (BankFieldProjection.machine (0 : Fin 2)).OutputsWithin
        item (projectWord item) (8 * (item.length + 1)) := by
    intro item _
    exact BankFieldProjection.outputs (0 : Fin 2) item
  have h := SourceListMachineOuterFramed.outputsWithin
    (BankFieldProjection.machine (0 : Fin 2))
    (sourceItems source) projectWord
    (fun item => 8 * (item.length + 1)) hitem
  have hmap : (sourceItems source).map projectWord =
      tupleWords source := by
    simp [sourceItems, tupleWords,
      CodeDCanonicalSourceV2.canonicalSource, List.map_map,
      projectWord, CodeDCanonicalSourceV2.canonicalEntry,
      CodeDSourceCodecV2.encodeEntry, CodeDCodecV2.encodeItems]
  rw [hmap] at h
  simpa only [tupleMachine, tupleClock,
    CodeDCanonicalSourceV2.encodedSource,
    CodeDSourceCodecV2.encodeSource, CodeDCodecV2.encodeItems,
    sourceItems] using h

def alphabetItems (alphabet : Array (Nat × ℚ)) : List (List Bool) :=
  alphabet.toList.map CodeDTargetV2.alphabetEntry

def labelWords (alphabet : Array (Nat × ℚ)) : List (List Bool) :=
  alphabet.toList.map (fun x => x.1.bits)

noncomputable def alphabetMachine : Machine :=
  SourceListMachineOuterFramed.machine
    (BankFieldProjection.machine (0 : Fin 2))

noncomputable def alphabetClock (alphabet : Array (Nat × ℚ)) : Nat :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine
      (BankFieldProjection.machine (0 : Fin 2)))
    (alphabetItems alphabet)
    (SourceListMachineOuterFramed.framedOutput projectWord)
    (SourceListMachineOuterFramed.framedBound projectWord
      (fun item => 8 * (item.length + 1)))

theorem project_alphabet_labels (alphabet : Array (Nat × ℚ)) :
    alphabetMachine.OutputsWithin
      (CodeDTargetV2.alphabetBytes alphabet)
      (SourceListEncoding.encode (labelWords alphabet))
      (alphabetClock alphabet) := by
  have hitem : ∀ item ∈ alphabetItems alphabet,
      (BankFieldProjection.machine (0 : Fin 2)).OutputsWithin
        item (projectWord item) (8 * (item.length + 1)) := by
    intro item _
    exact BankFieldProjection.outputs (0 : Fin 2) item
  have h := SourceListMachineOuterFramed.outputsWithin
    (BankFieldProjection.machine (0 : Fin 2))
    (alphabetItems alphabet) projectWord
    (fun item => 8 * (item.length + 1)) hitem
  have hmap : (alphabetItems alphabet).map projectWord =
      labelWords alphabet := by
    simp [alphabetItems, labelWords, List.map_map, projectWord,
      CodeDTargetV2.alphabetEntry]
  rw [hmap] at h
  simpa only [alphabetMachine, alphabetClock,
    CodeDTargetV2.alphabetBytes, CodeDCodecV2.encodeItems,
    alphabetItems] using h

#print axioms project_source_tuple
#print axioms project_alphabet_labels

end CurrentAdditive.CylinderProductionProjection
