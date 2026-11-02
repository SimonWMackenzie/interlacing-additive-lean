import CurrentAdditive.BinaryGCDBound
import EthInapproximability.CurrentPaper.BitMachineBankWrapper
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-! A framed single-input version of the raw physical GCD controller. -/
namespace CurrentAdditive.BinaryGCDPacket

open Turing
open EthInapproximability.CurrentPaper
open CurrentAdditive.BinaryGCDCore CurrentAdditive.BinaryGCDBound
open BitMachineEncoding

def inputBank (input divisor : List Bool) : BitMachineBankCodec.Bank 7 :=
  bank input divisor [] [] [] [] []

def inputPacket (input divisor : List Bool) : List Bool :=
  BitMachineBankCodec.encode (inputBank input divisor)

noncomputable def machine : BitMachine.Machine :=
  BitMachineBankWrapper.machine program .checkDivisor initial

def rawPush : Nat := BitMachineStackGrowth.perStep program

def outputBound (N : Nat) : Nat :=
  14 * (N + rawPush * startClock N) + 7

def packetClock (N : Nat) : Nat :=
  15 * (2 * N + 8) + startClock N + 2 * outputBound N + 4

theorem inputPacket_length (input divisor : List Bool) :
    (inputPacket input divisor).length =
      2 * (input.length + divisor.length) + 7 := by
  simpa [inputPacket, inputBank, bank] using
    BitMachineBinaryDivision.initialBank_code_length input divisor

private theorem input_word_length_le (input divisor : List Bool) (j : Fin 7) :
    (inputBank input divisor j).length ≤ input.length + divisor.length := by
  fin_cases j <;> simp [inputBank, bank, BitMachineBinaryDivision.bank] <;> omega

theorem final_code_length_le (input divisor : List Bool)
    (t : Nat) (c : Config)
    (ht : t ≤ startClock (input.length + divisor.length))
    (hr : run t
      (cfg (some .checkDivisor) initial input divisor [] [] [] [] []) = c) :
    (BitMachineBankCodec.encode c.stk).length ≤
      outputBound (input.length + divisor.length) := by
  let N := input.length + divisor.length
  have hlen (j : Fin 7) :
      (c.stk j).length ≤ N + rawPush * startClock N := by
    have hg := BitMachineStackGrowth.run_growth program
      (cfg (some .checkDivisor) initial input divisor [] [] [] [] []) t j
    change ((run t (cfg (some .checkDivisor) initial input divisor [] [] [] [] [])).stk j).length ≤
      (inputBank input divisor j).length + rawPush * t at hg
    rw [hr] at hg
    have hi := input_word_length_le input divisor j
    have ht' : t ≤ startClock N := ht
    have hm := Nat.mul_le_mul_left rawPush ht'
    omega
  have hsum : (∑ j : Fin 7, (c.stk j).length) ≤
      7 * (N + rawPush * startClock N) := by
    calc
      _ ≤ ∑ _ : Fin 7, (N + rawPush * startClock N) := by
        exact Finset.sum_le_sum (by intro j _; exact hlen j)
      _ = _ := by simp
  rw [BitMachineBankCodec.encode_length]
  unfold outputBound
  dsimp [N] at hsum ⊢
  omega

theorem packet_outputs (input divisor : List Bool) :
    ∃ (output : List Bool),
      machine.OutputsWithin (inputPacket input divisor) output
        (packetClock (input.length + divisor.length)) ∧
      ∃ (S : BitMachineBankCodec.Bank 7),
        output = BitMachineBankCodec.encode S ∧
        (0 < EncodedCommunication.bitsValue divisor →
          EncodedCommunication.bitsValue (S 1) =
            Nat.gcd (BitMachineBinaryDivision.msbValue input)
              (EncodedCommunication.bitsValue divisor)) := by
  obtain ⟨t, c, ht, hr, hc, hv⟩ := raw_total input divisor
  have hdecode : BitMachineBankCodec.decode 7 (inputPacket input divisor) =
      some (inputBank input divisor) := by simp [inputPacket]
  have hraw : ((advance program)^[t])
      (⟨some Label.checkDivisor, initial, inputBank input divisor⟩ : Config) = c := by
    simpa [run, cfg, inputBank, bank] using hr
  obtain ⟨u, S', hu, hpacked⟩ := BitMachineBankWrapper.packed_run
    program .checkDivisor initial (inputPacket input divisor)
    (inputBank input divisor) hdecode t c hraw hc
  let output := BitMachineBankCodec.encode c.stk
  have hencode : BitMachineBankSerialize.encode (List.ofFn c.stk) = output := by
    dsimp [output]
    rw [BitMachineBankCodec.encode_eq_list]
    rfl
  rw [hencode] at hu hpacked
  have hsize := final_code_length_le input divisor t c ht hr
  have hclock : u ≤ packetClock (input.length + divisor.length) := by
    rw [inputPacket_length] at hu
    unfold packetClock
    change output.length ≤ outputBound (input.length + divisor.length) at hsize
    omega
  refine ⟨output, ?_, c.stk, rfl, ?_⟩
  · change (BitMachineBankWrapper.machine program .checkDivisor initial).OutputsWithin
      (inputPacket input divisor) output (packetClock (input.length + divisor.length))
    apply outputsWithin_of_raw_run (.inr 0) (.inr 2)
      (.inr (.parse (.scan 0))) (initial, none)
      (BitMachineBankWrapper.program program .checkDivisor initial)
      (inputPacket input divisor) output u _ hclock
    · rw [BitMachineBankWrapper.initial_cfg]
      change (BitMachineBankWrapper.run program .checkDivisor initial u _).l = none
      rw [hpacked]
      rfl
    · rw [BitMachineBankWrapper.initial_cfg]
      change (BitMachineBankWrapper.run program .checkDivisor initial u _).stk
        (.inr 2) = output
      rw [hpacked]
      rfl
  · exact hv

end CurrentAdditive.BinaryGCDPacket
