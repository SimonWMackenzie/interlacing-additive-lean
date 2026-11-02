import EthInapproximability.CurrentPaper.BitMachineBinaryDivision
import EthInapproximability.CurrentPaper.PrimeSamplerEntryAlgorithm

/-!
# One binary base-prime digit query

Source: locked v8 `B-effectivity-details.tex`,
`lem:paper-explicit-balanced-family`. This module instantiates the proved
physical binary divider on a canonical packed query: the label word is
LSB-first in the sampler representation, but the divider visits its reversal
MSB first. The divisor is a positive LSB-first prime word.

The output packet contains both quotient and remainder, each as an LSB-first
word. It is one base-prime coefficient extraction, not yet the iterated
`t`-coefficient decoder or modular Horner evaluator.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerBinaryDigit

open BitMachineBinaryDivision

theorem msbValue_reverse (bits : List Bool) :
    msbValue bits.reverse = EncodedCommunication.bitsValue bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
      simp only [List.reverse_cons, msbValue, List.foldl_append,
        List.foldl_cons, List.foldl_nil, EncodedCommunication.bitsValue]
      rw [← msbValue, ih]

def queryPacket (labelBits primeBits : List Bool) : List Bool :=
  packedInput labelBits.reverse primeBits

def answerPacket (labelBits primeBits : List Bool) : List Bool :=
  BitMachineBankCodec.encode (finalBank labelBits.reverse primeBits)

/-- One literal division call has a quadratic bound in the total length of
the label and modulus words. `field` framing contributes only seven constant
markers and a factor two. -/
theorem query_outputs (labelBits primeBits : List Bool) :
    packedMachine.OutputsWithin (queryPacket labelBits primeBits)
      (answerPacket labelBits primeBits)
      (100 * ((queryPacket labelBits primeBits).length + 1) ^ 2) := by
  exact packed_outputs labelBits.reverse primeBits

theorem query_length (labelBits primeBits : List Bool) :
    (queryPacket labelBits primeBits).length =
      2 * (labelBits.length + primeBits.length) + 7 := by
  simpa only [queryPacket, List.length_reverse] using
    initialBank_code_length labelBits.reverse primeBits

/-- The decoded quotient and remainder are the numerical base-prime step.
This includes leading-zero input words. A zero divisor is excluded. -/
theorem query_semantics (labelBits primeBits : List Bool)
    (hp : 0 < EncodedCommunication.bitsValue primeBits) :
    let bank := finalBank labelBits.reverse primeBits
    EncodedCommunication.bitsValue (bank 2) =
        EncodedCommunication.bitsValue labelBits %
          EncodedCommunication.bitsValue primeBits ∧
      EncodedCommunication.bitsValue (bank 3) =
        EncodedCommunication.bitsValue labelBits /
          EncodedCommunication.bitsValue primeBits := by
  have hs := standard_division_spec labelBits.reverse primeBits hp
  rw [msbValue_reverse] at hs
  simpa [finalBank, bank] using ⟨hs.2, hs.1⟩

theorem answer_decodes (labelBits primeBits : List Bool) :
    BitMachineBankCodec.decode 7 (answerPacket labelBits primeBits) =
      some (finalBank labelBits.reverse primeBits) := by
  simp [answerPacket]

/-- The machine's two numerical output banks are exactly the recursive
quotient and final coefficient in the locked prime-family decoder. Repeating
this step and physically constructing a coefficient stream are still separate
from this one-call theorem. -/
theorem coefficient_step (p t l : ℕ) (hp : 0 < p) :
    let bank := finalBank l.bits.reverse p.bits
    PrimeSamplerEntryAlgorithm.coefficients p (t + 1) l =
      PrimeSamplerEntryAlgorithm.coefficients p t
        (EncodedCommunication.bitsValue (bank 3)) ++
        [EncodedCommunication.bitsValue (bank 2)] := by
  have hpbits : EncodedCommunication.bitsValue p.bits = p := by simp
  have hlbits : EncodedCommunication.bitsValue l.bits = l := by simp
  have hs := query_semantics l.bits p.bits (by simpa [hpbits] using hp)
  dsimp only at hs
  simp only [hpbits, hlbits] at hs
  simp [PrimeSamplerEntryAlgorithm.coefficients, hs.1, hs.2]

end EthInapproximability.CurrentPaper.PrimeSamplerBinaryDigit
