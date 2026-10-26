import CurrentAdditive.GaussPacket
import CurrentAdditive.CodeDZeroWordV2
import EthInapproximability.CurrentPaper.BankFieldProjection

/-!
A physical pivot-candidate zero test for the existing canonical RawRat ABI.
The fixed program projects the numerator word from Bank3 and invokes the
already checked linear word scanner.  It is an all-input BitMachine.Machine;
the semantic theorem below identifies the single output bit on valid RawRat
packets.  It does not perform a matrix lookup or a pivot search by itself.
-/

namespace CurrentAdditive.GaussRawZeroCheck

open CurrentAdditive.CodeDCodec
open EthInapproximability.CurrentPaper

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition
    (BankFieldProjection.machine (1 : Fin 3))
    CurrentAdditive.CodeDZeroWordV2.machine

def numeratorWord (input : List Bool) : List Bool :=
  BankFieldProjection.result (1 : Fin 3) input

def result (input : List Bool) : List Bool :=
  [!((numeratorWord input).any id)]

def clock (input : List Bool) : Nat :=
  10 * (input.length + 1) + 2 * (numeratorWord input).length + 2 +
    ((numeratorWord input).length + 2)

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (result input) (clock input) := by
  have hp := BankFieldProjection.outputs (1 : Fin 3) input
  have hz := CurrentAdditive.CodeDZeroWordV2.outputs (numeratorWord input)
  have h := BitMachineComposition.composition_outputsWithin
    (BankFieldProjection.machine (1 : Fin 3))
    CurrentAdditive.CodeDZeroWordV2.machine hp hz
  simpa only [machine, clock, result, numeratorWord] using h

theorem numerator_encodeRawRat (r : RawRat) :
    numeratorWord (encodeRawRat r) = r.numerator := by
  simp [numeratorWord, BankFieldProjection.result_encode,
    encodeRawRat, rawRatBank]

theorem zero_flag_iff_value (r : RawRat) (hvalid : r.Valid) :
    result (encodeRawRat r) = [true] ↔ r.value = 0 := by
  rw [show result (encodeRawRat r) = [!r.numerator.any id] by
    simp [result, numerator_encodeRawRat]]
  have hbits := CurrentAdditive.CodeDZeroWordV2.output_true_iff_zero r.numerator
  have hd : (BitMachineBinaryMultiply.msbValue r.denominator : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hvalid
  have hn : [!r.numerator.any id] = [true] ↔
      EncodedCommunication.bitsValue r.numerator = 0 := by
    simpa using hbits
  rw [hn]
  cases hsign : r.negative <;>
    simp [RawRat.value, hsign, div_eq_zero_iff, hd]

theorem clock_le_linear (input : List Bool) :
    clock input ≤ 14 * (input.length + 1) := by
  have h := BankFieldProjection.result_length (1 : Fin 3) input
  change (numeratorWord input).length ≤ input.length at h
  unfold clock
  omega

#print axioms outputs
#print axioms zero_flag_iff_value
#print axioms clock_le_linear

end CurrentAdditive.GaussRawZeroCheck
