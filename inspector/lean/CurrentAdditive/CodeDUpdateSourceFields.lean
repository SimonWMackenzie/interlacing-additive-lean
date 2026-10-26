import CurrentAdditive.CodeDUpdateProductPairFields
import EthInapproximability.CurrentPaper.BitMachineComposition
import EthInapproximability.CurrentPaper.SourceFieldWriter

/-! Reusable physical projections retaining the source entry and its old weight. -/

namespace CurrentAdditive.CodeDUpdateSourceFields

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CodeDUpdateProductPairFields CodeDSourceCodecV2 CodeDCanonicalSourceV2 CodeDCodec

def oldEntryWord (x : List Bool) : List Bool :=
  BankFieldProjection.result (0 : Fin 3) x

def oldWeightWord (x : List Bool) : List Bool :=
  BankFieldProjection.result (1 : Fin 2) (oldEntryWord x)

noncomputable def oldEntryMachine : BitMachine.Machine :=
  BitMachineComposition.composition
    (BankFieldProjection.machine (0 : Fin 3))
    SourceFieldWriter.fieldMachine

noncomputable def oldWeightMachine : BitMachine.Machine :=
  BitMachineComposition.composition
    (BitMachineComposition.composition
      (BankFieldProjection.machine (0 : Fin 3))
      (BankFieldProjection.machine (1 : Fin 2)))
    SourceFieldWriter.fieldMachine

def oldEntryField (x : List Bool) : List Bool := field (oldEntryWord x)
def oldWeightField (x : List Bool) : List Bool := field (oldWeightWord x)

noncomputable def oldEntryClock (x : List Bool) : Nat :=
  (2*3+4)*(x.length+1)+2*(oldEntryWord x).length+2+
    (4*(oldEntryWord x).length+4)

noncomputable def oldWeightClock (x : List Bool) : Nat :=
  (2*3+4)*(x.length+1)+2*(oldEntryWord x).length+2+
  (2*2+4)*((oldEntryWord x).length+1)+2*(oldWeightWord x).length+2+
    (4*(oldWeightWord x).length+4)

theorem oldEntry_outputs (x : List Bool) :
    oldEntryMachine.OutputsWithin x (oldEntryField x)
      (oldEntryClock x) := by
  have h := BitMachineComposition.composition_outputsWithin
    (BankFieldProjection.machine (0 : Fin 3))
    SourceFieldWriter.fieldMachine
    (BankFieldProjection.outputs (0 : Fin 3) x)
    (SourceFieldWriter.field_outputs (oldEntryWord x))
  simpa only [oldEntryMachine, oldEntryField,
    oldEntryClock, oldEntryWord] using h

theorem oldWeight_outputs (x : List Bool) :
    oldWeightMachine.OutputsWithin x (oldWeightField x)
      (oldWeightClock x) := by
  have h₁ := BitMachineComposition.composition_outputsWithin
    (BankFieldProjection.machine (0 : Fin 3))
    (BankFieldProjection.machine (1 : Fin 2))
    (BankFieldProjection.outputs (0 : Fin 3) x)
    (BankFieldProjection.outputs (1 : Fin 2) (oldEntryWord x))
  have h₂ := BitMachineComposition.composition_outputsWithin
    (BitMachineComposition.composition
      (BankFieldProjection.machine (0 : Fin 3))
      (BankFieldProjection.machine (1 : Fin 2)))
    SourceFieldWriter.fieldMachine h₁
    (SourceFieldWriter.field_outputs (oldWeightWord x))
  simpa only [oldWeightMachine, oldWeightField,
    oldWeightClock, oldEntryWord, oldWeightWord] using h₂

theorem oldEntry_request (old : Entry) (lambda coefficient : ℚ) :
    oldEntryWord (requestPacket old lambda coefficient) = encodeEntry old := by
  simp only [oldEntryWord, requestPacket, BankFieldProjection.result_encode]
  simp

theorem oldWeight_request (old : Entry) (lambda coefficient : ℚ) :
    oldWeightWord (requestPacket old lambda coefficient) = encodeRawRat old.weight := by
  rw [show oldWeightWord (requestPacket old lambda coefficient) =
      BankFieldProjection.result (1 : Fin 2)
        (oldEntryWord (requestPacket old lambda coefficient)) by rfl]
  rw [oldEntry_request]
  simp [encodeEntry]

#print axioms oldEntry_outputs
#print axioms oldWeight_outputs
#print axioms oldWeight_request

end CurrentAdditive.CodeDUpdateSourceFields
