import CurrentAdditive.CodeDZeroWordV2
import CurrentAdditive.CodeDSourceCodecV2
import EthInapproximability.CurrentPaper.BankFieldProjection
import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
A concrete three-stage program for testing whether a serialized indexed
source entry has zero weight. The first two stages physically project the
Bank2 weight field and the Bank3 numerator field; the third scans every bit.
This is a predicate component for the later source-compaction pass, not a
claim that compaction has already been implemented.
-/

namespace CurrentAdditive.CodeDZeroEntryV2

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open CodeDCodec CodeDSourceCodecV2

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition
    (BitMachineComposition.composition
      (BankFieldProjection.machine (1 : Fin 2))
      (BankFieldProjection.machine (1 : Fin 3)))
    CodeDZeroWordV2.machine

def weightPacket (input : List Bool) : List Bool :=
  BankFieldProjection.result (1 : Fin 2) input

def numeratorWord (input : List Bool) : List Bool :=
  BankFieldProjection.result (1 : Fin 3) (weightPacket input)

def result (input : List Bool) : List Bool :=
  [!((numeratorWord input).any id)]

def clock (input : List Bool) : Nat :=
  let a := weightPacket input
  let b := numeratorWord input
  8 * (input.length + 1) + 2 * a.length + 2 +
    10 * (a.length + 1) + 2 * b.length + 2 + (b.length + 2)

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (result input) (clock input) := by
  have h₁ := BankFieldProjection.outputs (1 : Fin 2) input
  have h₂ := BankFieldProjection.outputs (1 : Fin 3) (weightPacket input)
  have h₃ := CodeDZeroWordV2.outputs (numeratorWord input)
  have h₁₂ := BitMachineComposition.composition_outputsWithin
    (BankFieldProjection.machine (1 : Fin 2))
    (BankFieldProjection.machine (1 : Fin 3)) h₁ h₂
  have h := BitMachineComposition.composition_outputsWithin
    (BitMachineComposition.composition
      (BankFieldProjection.machine (1 : Fin 2))
      (BankFieldProjection.machine (1 : Fin 3)))
    CodeDZeroWordV2.machine h₁₂ h₃
  simpa only [machine, clock, result, weightPacket, numeratorWord] using h

theorem numerator_encodeEntry (entry : Entry) :
    numeratorWord (encodeEntry entry) = entry.weight.numerator := by
  simp [numeratorWord, weightPacket, encodeEntry,
    BankFieldProjection.result_encode, encodeRawRat, rawRatBank]

theorem zero_flag_iff_numerator (entry : Entry) :
    result (encodeEntry entry) = [true] ↔
      EncodedCommunication.bitsValue entry.weight.numerator = 0 := by
  simpa [result, numerator_encodeEntry] using
    CodeDZeroWordV2.output_true_iff_zero entry.weight.numerator

theorem zero_flag_iff_value (entry : Entry) (hvalid : entry.weight.Valid) :
    result (encodeEntry entry) = [true] ↔ entry.weight.value = 0 := by
  rw [zero_flag_iff_numerator]
  have hd : (BitMachineBinaryMultiply.msbValue entry.weight.denominator : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hvalid
  cases hsign : entry.weight.negative <;>
    simp [RawRat.value, hsign, div_eq_zero_iff, hd]

theorem clock_le_linear (input : List Bool) :
    clock input ≤ 24 * (input.length + 1) := by
  have ha := BankFieldProjection.result_length (1 : Fin 2) input
  have hb := BankFieldProjection.result_length (1 : Fin 3) (weightPacket input)
  change (weightPacket input).length ≤ input.length at ha
  change
    8 * (input.length + 1) + 2 * (weightPacket input).length + 2 +
      10 * ((weightPacket input).length + 1) +
      2 * (numeratorWord input).length + 2 +
      ((numeratorWord input).length + 2) ≤
        24 * (input.length + 1)
  change (numeratorWord input).length ≤ (weightPacket input).length at hb
  omega

#print axioms outputs
#print axioms zero_flag_iff_numerator
#print axioms zero_flag_iff_value
#print axioms clock_le_linear

end CurrentAdditive.CodeDZeroEntryV2
