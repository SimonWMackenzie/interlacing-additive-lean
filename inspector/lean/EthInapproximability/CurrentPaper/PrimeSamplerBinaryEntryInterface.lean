import EthInapproximability.CurrentPaper.PrimeSamplerBinaryQueryMachine
import EthInapproximability.CurrentPaper.BankFieldProjection
import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
# Ordinary-word interface to the binary prime-family accessor

Source: locked v8 Appendix B, `lem:paper-explicit-balanced-family`.
The paper numbers polynomial labels and coordinates from one: its `ℓ,j`
are represented here by the zero-based binary words for `ℓ-1,j-1`.
The output word represents the zero-based colour `c_ℓ(j)-1`.

The fixed 23-bank query machine first writes a complete encoded packet.
The second fixed machine parses that packet and physically transfers field
18 to an ordinary output stack. The composition charges both executions
and the intervening two linear transfers; field extraction is not a free
host-language projection. Words are least-significant-bit first, as in
`EncodedCommunication.bitsValue`. The degree is a semantic domain guard,
not a loop counter or an expanded unary input.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerBinaryEntryInterface

open PrimeSamplerBinaryQueryMachine

def entryPacket (labelBits prime coordinate alphabet : List Bool) : List Bool :=
  BitMachineBankCodec.encode (finalBank labelBits prime coordinate alphabet)

def entryWord (labelBits prime coordinate alphabet : List Bool) : List Bool :=
  BankFieldProjection.result (18 : Fin 23)
    (entryPacket labelBits prime coordinate alphabet)

theorem entryWord_eq (labelBits prime coordinate alphabet : List Bool) :
    entryWord labelBits prime coordinate alphabet =
      resultWord labelBits prime coordinate alphabet := by
  simp [entryWord, entryPacket, finalBank, bank, resultWord]

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition packedMachine
    (BankFieldProjection.machine (18 : Fin 23))

/-- One fixed machine writes the ordinary answer word. The displayed
bound includes packet writing, two inter-machine transfers, packet parsing,
and extraction of the selected field. -/
theorem outputs_packet (labelBits prime coordinate alphabet : List Bool)
    (hp : 2 ≤ EncodedCommunication.bitsValue prime) :
    machine.OutputsWithin
      (packedInput labelBits prime coordinate alphabet)
      (entryWord labelBits prime coordinate alphabet)
      (10000 * ((packedInput labelBits prime coordinate alphabet).length + 1) ^ 3 +
        2 * (entryPacket labelBits prime coordinate alphabet).length + 2 +
        50 * ((entryPacket labelBits prime coordinate alphabet).length + 1)) := by
  have hQ := packed_outputs labelBits prime coordinate alphabet hp
  have hP := BankFieldProjection.outputs (18 : Fin 23)
    (entryPacket labelBits prime coordinate alphabet)
  exact BitMachineComposition.composition_outputsWithin packedMachine
    (BankFieldProjection.machine (18 : Fin 23)) hQ hP

/-- Polynomial in the *input packet bitlength*, not in the numerical
values of the label, degree, prime, or coordinate. -/
theorem outputs_poly (labelBits prime coordinate alphabet : List Bool)
    (hp : 2 ≤ EncodedCommunication.bitsValue prime) :
    machine.OutputsWithin
      (packedInput labelBits prime coordinate alphabet)
      (entryWord labelBits prime coordinate alphabet)
      (12000 * ((packedInput labelBits prime coordinate alphabet).length + 1) ^ 3) := by
  have h := outputs_packet labelBits prime coordinate alphabet hp
  have hlen := finalBank_code_length_le labelBits prime coordinate alphabet hp
  have hin := initialBank_code_length labelBits prime coordinate alphabet
  apply BitMachine.outputsWithin_mono machine h
  let N := labelBits.length + prime.length + coordinate.length + alphabet.length
  change (entryPacket labelBits prime coordinate alphabet).length ≤
    20 * (N + 1) at hlen
  change (packedInput labelBits prime coordinate alphabet).length = 2 * N + 23 at hin
  rw [hin]
  dsimp only [entryPacket] at hlen ⊢
  have hx : 1 ≤ 2 * N + 24 := by omega
  have hpow : 1 ≤ (2 * N + 24) ^ 2 := by nlinarith
  have hcubic : N + 1 ≤ (2 * N + 24) ^ 3 := by
    calc
      N + 1 ≤ 2 * N + 24 := by omega
      _ = (2 * N + 24) * 1 := by omega
      _ ≤ (2 * N + 24) * (2 * N + 24) ^ 2 :=
        Nat.mul_le_mul_left _ hpow
      _ = (2 * N + 24) ^ 3 := by ring
  nlinarith

/-- The actual output word denotes the indexed prime-family entry,
subject to the prime, positive-alphabet, and label-domain hypotheses. -/
theorem entry_value (labelBits prime coordinate alphabet : List Bool)
    (hp : 2 ≤ EncodedCommunication.bitsValue prime)
    (hm : 0 < EncodedCommunication.bitsValue alphabet)
    (degree : ℕ)
    (hlabel : EncodedCommunication.bitsValue labelBits <
      EncodedCommunication.bitsValue prime ^ degree) :
    EncodedCommunication.bitsValue
      (entryWord labelBits prime coordinate alphabet) =
      PrimeSampler.entry
        (EncodedCommunication.bitsValue prime) degree
        (EncodedCommunication.bitsValue alphabet)
        (EncodedCommunication.bitsValue labelBits)
        (EncodedCommunication.bitsValue coordinate) := by
  rw [entryWord_eq]
  simpa [finalBank, bank] using
    (answer_entry_value labelBits prime coordinate alphabet hp hm degree hlabel)

/-- With paper indices `ℓ,j ≥ 1`, the word for `ℓ-1,j-1` returns
`c_ℓ(j)-1`. Adding one gives precisely the displayed Appendix-B entry. -/
theorem paper_one_based_value (p degree m ℓ j : ℕ)
    (hp : 2 ≤ p) (hm : 0 < m)
    (hlabel : ℓ - 1 < p ^ degree) :
    EncodedCommunication.bitsValue
      (entryWord (ℓ - 1).bits p.bits (j - 1).bits m.bits) + 1 =
      1 + (((∑ r ∈ Finset.range degree,
        ((ℓ - 1) / p ^ r % p) * (j - 1) ^ r) % p) % m) := by
  have hv := entry_value (ℓ - 1).bits p.bits (j - 1).bits m.bits
    (by simpa using hp) (by simpa using hm) degree (by simpa using hlabel)
  simp only [EncodedCommunication.bitsValue_bits, PrimeSampler.entry_eq] at hv
  omega

end EthInapproximability.CurrentPaper.PrimeSamplerBinaryEntryInterface
