import CurrentAdditive.CodeDTargetV2
import EthInapproximability.CurrentPaper.BankFieldProjection
import EthInapproximability.CurrentPaper.SourceListMachineOuterFramed

/-! Physical extraction of the ordered label list from Code D's actual
alphabet packet.  Repeated labels remain distinct indexed items. -/

namespace CurrentAdditive.CylinderAlphabetProjection

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine

def inputItems (alphabet : Array (Nat × ℚ)) : List (List Bool) :=
  alphabet.toList.map CodeDTargetV2.alphabetEntry

def labelWords (alphabet : Array (Nat × ℚ)) : List (List Bool) :=
  alphabet.toList.map (fun x => x.1.bits)

def projectLabel (item : List Bool) : List Bool :=
  BankFieldProjection.result (0 : Fin 2) item

noncomputable def projectMachine : Machine :=
  SourceListMachineOuterFramed.machine
    (BankFieldProjection.machine (0 : Fin 2))

noncomputable def projectClock (alphabet : Array (Nat × ℚ)) : Nat :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine
      (BankFieldProjection.machine (0 : Fin 2)))
    (inputItems alphabet)
    (SourceListMachineOuterFramed.framedOutput projectLabel)
    (SourceListMachineOuterFramed.framedBound projectLabel
      (fun item => 8 * (item.length + 1)))

theorem projectLabel_entry (entry : Nat × ℚ) :
    projectLabel (CodeDTargetV2.alphabetEntry entry) = entry.1.bits := by
  simp [projectLabel, CodeDTargetV2.alphabetEntry]

theorem project_output (alphabet : Array (Nat × ℚ)) :
    projectMachine.OutputsWithin (CodeDTargetV2.alphabetBytes alphabet)
      (SourceListEncoding.encode (labelWords alphabet))
      (projectClock alphabet) := by
  have hitem : ∀ item ∈ inputItems alphabet,
      (BankFieldProjection.machine (0 : Fin 2)).OutputsWithin
        item (projectLabel item) (8 * (item.length + 1)) := by
    intro item _
    exact BankFieldProjection.outputs (0 : Fin 2) item
  have h := SourceListMachineOuterFramed.outputsWithin
    (BankFieldProjection.machine (0 : Fin 2)) (inputItems alphabet)
    projectLabel (fun item => 8 * (item.length + 1)) hitem
  have hmap : (inputItems alphabet).map projectLabel = labelWords alphabet := by
    simp [inputItems, labelWords, List.map_map, projectLabel_entry]
  rw [hmap] at h
  simpa only [projectMachine, projectClock, CodeDTargetV2.alphabetBytes,
    CodeDCodecV2.encodeItems, inputItems] using h

#print axioms project_output

end CurrentAdditive.CylinderAlphabetProjection
