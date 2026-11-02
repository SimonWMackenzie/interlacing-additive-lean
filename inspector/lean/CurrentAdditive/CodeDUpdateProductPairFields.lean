import CurrentAdditive.CodeDUpdatedEntryFields
import CurrentAdditive.CodeDPairProductTargetV2
import EthInapproximability.CurrentPaper.BitMachineComposition
import EthInapproximability.CurrentPaper.SourceFieldWriter

/-! Physical λ/coefficient request fields, retaining the old Entry in the input. -/

namespace CurrentAdditive.CodeDUpdateProductPairFields

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CodeDSourceCodecV2 CodeDCanonicalSourceV2 CodeDCodec

def requestPacket (old : Entry) (lambda coefficient : ℚ) : List Bool :=
  BitMachineBankCodec.encode (fun i : Fin 3 =>
    if i = 0 then encodeEntry old else
    if i = 1 then encodeRawRat (rawOfRat lambda) else
      encodeRawRat (rawOfRat coefficient))

def lambdaWord (x : List Bool) : List Bool :=
  BankFieldProjection.result (1 : Fin 3) x

def coefficientWord (x : List Bool) : List Bool :=
  BankFieldProjection.result (2 : Fin 3) x

noncomputable def lambdaMachine : BitMachine.Machine :=
  BitMachineComposition.composition
    (BankFieldProjection.machine (1 : Fin 3))
    SourceFieldWriter.fieldMachine

noncomputable def coefficientMachine : BitMachine.Machine :=
  BitMachineComposition.composition
    (BankFieldProjection.machine (2 : Fin 3))
    SourceFieldWriter.fieldMachine

def lambdaField (x : List Bool) : List Bool := field (lambdaWord x)
def coefficientField (x : List Bool) : List Bool := field (coefficientWord x)

noncomputable def lambdaClock (x : List Bool) : Nat :=
  (2*3+4)*(x.length+1)+2*(lambdaWord x).length+2+
    (4*(lambdaWord x).length+4)

noncomputable def coefficientClock (x : List Bool) : Nat :=
  (2*3+4)*(x.length+1)+2*(coefficientWord x).length+2+
    (4*(coefficientWord x).length+4)

theorem lambda_outputs (x : List Bool) :
    lambdaMachine.OutputsWithin x (lambdaField x) (lambdaClock x) := by
  have h := BitMachineComposition.composition_outputsWithin
    (BankFieldProjection.machine (1 : Fin 3))
    SourceFieldWriter.fieldMachine
    (BankFieldProjection.outputs (1 : Fin 3) x)
    (SourceFieldWriter.field_outputs (lambdaWord x))
  simpa only [lambdaMachine, lambdaField, lambdaClock, lambdaWord] using h

theorem coefficient_outputs (x : List Bool) :
    coefficientMachine.OutputsWithin x (coefficientField x)
      (coefficientClock x) := by
  have h := BitMachineComposition.composition_outputsWithin
    (BankFieldProjection.machine (2 : Fin 3))
    SourceFieldWriter.fieldMachine
    (BankFieldProjection.outputs (2 : Fin 3) x)
    (SourceFieldWriter.field_outputs (coefficientWord x))
  simpa only [coefficientMachine, coefficientField,
    coefficientClock, coefficientWord] using h

theorem fields_request (old : Entry) (lambda coefficient : ℚ) :
    lambdaField (requestPacket old lambda coefficient) ++
      coefficientField (requestPacket old lambda coefficient) =
    CodeDPairProductTargetV2.pairBytes
      (rawOfRat lambda) (rawOfRat coefficient) := by
  have hLam : lambdaWord (requestPacket old lambda coefficient) =
      encodeRawRat (rawOfRat lambda) := by
    simp only [lambdaWord, requestPacket,
      BankFieldProjection.result_encode]
    simp
  have hc : coefficientWord (requestPacket old lambda coefficient) =
      encodeRawRat (rawOfRat coefficient) := by
    simp only [coefficientWord, requestPacket,
      BankFieldProjection.result_encode]
    simp
  rw [show lambdaField (requestPacket old lambda coefficient) =
      field (encodeRawRat (rawOfRat lambda)) by simp [lambdaField, hLam]]
  rw [show coefficientField (requestPacket old lambda coefficient) =
      field (encodeRawRat (rawOfRat coefficient)) by simp [coefficientField, hc]]
  simp [CodeDPairProductTargetV2.pairBytes,
    CodeDPairProductTargetV2.pairBank, BitMachineBankCodec.encode_eq_list]

#print axioms lambda_outputs
#print axioms coefficient_outputs
#print axioms fields_request

end CurrentAdditive.CodeDUpdateProductPairFields
