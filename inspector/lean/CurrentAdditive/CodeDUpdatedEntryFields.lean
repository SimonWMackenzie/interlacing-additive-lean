import CurrentAdditive.CodeDUpdatedEntrySerializer
import EthInapproximability.CurrentPaper.BitMachineComposition
import EthInapproximability.CurrentPaper.SourceFieldWriter

/-! Two physical field producers called on the same old-entry/new-weight pair. -/

namespace CurrentAdditive.CodeDUpdatedEntryFields

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CodeDSourceCodecV2 CodeDCanonicalSourceV2 CodeDCodec

def pairPacket (old : Entry) (updated : ℚ) : List Bool :=
  BitMachineBankCodec.encode (fun i : Fin 2 =>
    if i = 0 then encodeEntry old else encodeRawRat (rawOfRat updated))

def outerOld (x : List Bool) : List Bool :=
  BankFieldProjection.result (0 : Fin 2) x

def oldWord (x : List Bool) : List Bool :=
  BankFieldProjection.result (0 : Fin 2) (outerOld x)

noncomputable def wordMachine : BitMachine.Machine :=
  BitMachineComposition.composition
    (BitMachineComposition.composition
      (BankFieldProjection.machine (0 : Fin 2))
      (BankFieldProjection.machine (0 : Fin 2)))
    SourceFieldWriter.fieldMachine

def wordField (x : List Bool) : List Bool :=
  field (oldWord x)

noncomputable def wordClock (x : List Bool) : Nat :=
  (2*2+4)*(x.length+1) + 2*(outerOld x).length+2 +
  (2*2+4)*((outerOld x).length+1) +
  2*(oldWord x).length+2 +
  (4*(oldWord x).length+4)

theorem word_outputs (x : List Bool) :
    wordMachine.OutputsWithin x (wordField x) (wordClock x) := by
  have h₁ := BitMachineComposition.composition_outputsWithin
    (BankFieldProjection.machine (0 : Fin 2))
    (BankFieldProjection.machine (0 : Fin 2))
    (BankFieldProjection.outputs (0 : Fin 2) x)
    (BankFieldProjection.outputs (0 : Fin 2) (outerOld x))
  have h₂ := BitMachineComposition.composition_outputsWithin
    (BitMachineComposition.composition
      (BankFieldProjection.machine (0 : Fin 2))
      (BankFieldProjection.machine (0 : Fin 2)))
    SourceFieldWriter.fieldMachine
    h₁ (SourceFieldWriter.field_outputs (oldWord x))
  simpa only [wordMachine, wordField, wordClock, outerOld, oldWord] using h₂

noncomputable def weightMachine : BitMachine.Machine :=
  BitMachineComposition.composition
    (BankFieldProjection.machine (1 : Fin 2))
    SourceFieldWriter.fieldMachine

def weightWord (x : List Bool) : List Bool :=
  BankFieldProjection.result (1 : Fin 2) x

def weightField (x : List Bool) : List Bool :=
  field (weightWord x)

noncomputable def weightClock (x : List Bool) : Nat :=
  (2*2+4)*(x.length+1)+2*(weightWord x).length+2+
    (4*(weightWord x).length+4)

theorem weight_outputs (x : List Bool) :
    weightMachine.OutputsWithin x (weightField x) (weightClock x) := by
  have h := BitMachineComposition.composition_outputsWithin
    (BankFieldProjection.machine (1 : Fin 2))
    SourceFieldWriter.fieldMachine
    (BankFieldProjection.outputs (1 : Fin 2) x)
    (SourceFieldWriter.field_outputs (weightWord x))
  simpa only [weightMachine, weightField, weightClock, weightWord] using h

theorem word_pair (old : Entry) (updated : ℚ) :
    wordField (pairPacket old updated) =
      field (CodeDCodecV2.encodeItems old.word) := by
  simp [wordField, oldWord, outerOld, pairPacket,
    BankFieldProjection.result_encode,
    encodeEntry]

theorem weight_pair (old : Entry) (updated : ℚ) :
    weightField (pairPacket old updated) =
      field (encodeRawRat (rawOfRat updated)) := by
  simp [weightField, weightWord, pairPacket,
    BankFieldProjection.result_encode]

theorem fields_pair (old : Entry) (updated : ℚ) :
    wordField (pairPacket old updated) ++
      weightField (pairPacket old updated) =
      encodeEntry ⟨old.word, rawOfRat updated⟩ := by
  rw [word_pair, weight_pair]
  simp [encodeEntry, BitMachineBankCodec.encode_eq_list]

#print axioms word_outputs
#print axioms weight_outputs
#print axioms fields_pair

end CurrentAdditive.CodeDUpdatedEntryFields
