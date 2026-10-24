import CurrentAdditive.BinaryGCDAllInput
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

namespace CurrentAdditive.BinaryGCDPolytime

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.BinaryGCDAllInput

def initialBank (S : Fin 7 → List Bool) :
    TM2.Cfg (fun _ : Fin 7 => Bool)
      (BitMachineRawSequence.Label (Fin 7) BinaryGCDCore.Label)
      ((Unit × Option Bool) × BinaryGCDCore.Control) :=
  ⟨some (BitMachineRawSequence.leftLabel (0 : Fin 7)),
    (((), none), BinaryGCDCore.initial), S⟩

def resultBank (S : Fin 7 → List Bool) : Fin 7 → List Bool :=
  (((advance program)^[clock (BitMachineBankCodec.encode S).length])
    (initialBank S)).stk

theorem result_correct (S : Fin 7 → List Bool) :
    (((advance program)^[clock (BitMachineBankCodec.encode S).length])
      (initialBank S)).l = none ∧
    (0 < EncodedCommunication.bitsValue (S 1) →
      EncodedCommunication.bitsValue (resultBank S 1) =
        Nat.gcd (BitMachineBinaryDivision.msbValue (S 0))
          (EncodedCommunication.bitsValue (S 1))) := by
  obtain ⟨t, c, ht, hr, hc, hv⟩ := BinaryGCDAllInput.raw_total S
  have hfixed : ((advance program)^[(clock (BitMachineBankCodec.encode S).length)])
      (initialBank S) = c := by
    rw [← Nat.sub_add_cancel ht, Function.iterate_add_apply]
    rw [show initialBank S =
      ⟨some (BitMachineRawSequence.leftLabel (0 : Fin 7)),
        (((), none), BinaryGCDCore.initial), S⟩ from rfl]
    rw [hr]
    exact BitMachineSubroutine.run_halted program c hc _
  rw [hfixed]
  exact ⟨hc, by simpa [resultBank, hfixed] using hv⟩

theorem clock_polynomial (N : Nat) :
    clock N ≤ 5000 * (N + 1)^4 := by
  unfold clock clearClock BinaryGCDBound.startClock BinaryGCDBound.roundClock
  nlinarith [sq_nonneg (N : ℤ)]

def rawPush : Nat := BitMachineStackGrowth.perStep program

def sizeCoefficient : Nat := 14 * (1 + rawPush * 5000) + 7

theorem result_length (S : Fin 7 → List Bool) :
    (BitMachineBankCodec.encode (resultBank S)).length ≤
      sizeCoefficient * ((BitMachineBankCodec.encode S).length + 1)^4 := by
  let N := (BitMachineBankCodec.encode S).length
  have hlen (j : Fin 7) :
      (resultBank S j).length ≤ N + rawPush * clock N := by
    have hg := BitMachineStackGrowth.run_growth program
      (initialBank S) (clock N) j
    change (resultBank S j).length ≤ (S j).length + rawPush * clock N at hg
    have hi := BitMachineBankCodec.word_length_le_encode S j
    omega
  have hsum : (∑ j : Fin 7, (resultBank S j).length) ≤
      7 * (N + rawPush * clock N) := by
    calc
      _ ≤ ∑ _ : Fin 7, (N + rawPush * clock N) := by
        exact Finset.sum_le_sum (by intro j _; exact hlen j)
      _ = _ := by simp
  have hc := clock_polynomial N
  have hpow : N ≤ (N+1)^4 := by
    nlinarith [sq_nonneg (N : ℤ), sq_nonneg ((N : ℤ)^2)]
  have hp1 : 1 ≤ (N+1)^4 := by
    nlinarith [sq_nonneg (N : ℤ), sq_nonneg ((N : ℤ)^2)]
  have hb : N + rawPush * clock N ≤
      (1 + rawPush * 5000) * (N+1)^4 := by
    have hm := Nat.mul_le_mul_left rawPush hc
    nlinarith [hpow]
  have hb14 := Nat.mul_le_mul_left 14 hb
  rw [BitMachineBankCodec.encode_length]
  change 2 * (∑ j : Fin 7, (resultBank S j).length) + 7 ≤
    (14 * (1 + rawPush * 5000) + 7) * (N+1)^4
  calc
    _ ≤ 14 * (N + rawPush * clock N) + 7 := by omega
    _ ≤ 14 * ((1 + rawPush * 5000) * (N+1)^4) + 7 := by omega
    _ ≤ (14 * (1 + rawPush * 5000) + 7) * (N+1)^4 := by
      nlinarith [hp1]

theorem polytime : BitMachine.Polytime (BitMachineBankWrapper.result resultBank) := by
  apply BitMachineBankWrapper.polytime program
    (BitMachineRawSequence.leftLabel (0 : Fin 7))
    (((), none), BinaryGCDCore.initial) resultBank
    5000 4 sizeCoefficient 4
  · intro S
    refine ⟨clock (BitMachineBankCodec.encode S).length,
      ((advance program)^[clock (BitMachineBankCodec.encode S).length])
        (initialBank S), clock_polynomial _, rfl, ?_, rfl⟩
    exact (result_correct S).1
  · exact result_length

end CurrentAdditive.BinaryGCDPolytime
