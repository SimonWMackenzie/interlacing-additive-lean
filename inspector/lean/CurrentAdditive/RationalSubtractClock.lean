import CurrentAdditive.RationalSubtractCore
import EthInapproximability.CurrentPaper.BitMachineBankWrapper

namespace EthInapproximability.CurrentPaper.RationalSubtractClock

open Turing BitMachineEncoding BitMachineStackEmbedding
open RationalSubtractCore

private theorem restricted12_size (ι : Fin 12 ↪ Fin 32) (S : Bank) :
    (BitMachineBankCodec.encode (restricted ι S)).length ≤
      25 * ((BitMachineBankCodec.encode S).length + 1) := by
  let n := (BitMachineBankCodec.encode S).length
  have hs : (∑ i : Fin 12, (restricted ι S i).length) ≤ ∑ _i : Fin 12, n :=
    Finset.sum_le_sum (by
      intro i _
      exact BitMachineBankCodec.word_length_le_encode S (ι i))
  rw [BitMachineBankCodec.encode_length]
  simp at hs
  omega

private theorem restricted9_size (ι : Fin 9 ↪ Fin 32) (S : Bank) :
    (BitMachineBankCodec.encode (fun i => S (ι i))).length ≤
      19 * ((BitMachineBankCodec.encode S).length + 1) := by
  let n := (BitMachineBankCodec.encode S).length
  have hs : (∑ i : Fin 9, (S (ι i)).length) ≤ ∑ _i : Fin 9, n :=
    Finset.sum_le_sum (by
      intro i _
      exact BitMachineBankCodec.word_length_le_encode S (ι i))
  rw [BitMachineBankCodec.encode_length]
  simp at hs
  omega

private theorem embedded12_size (ι : Fin 12 ↪ Fin 32) (S : Bank)
    (T : Fin 12 → List Bool) :
    (BitMachineBankCodec.encode (bank ι S T)).length ≤
      65 * ((BitMachineBankCodec.encode S).length +
        (BitMachineBankCodec.encode T).length + 1) := by
  let n := (BitMachineBankCodec.encode S).length
  let m := (BitMachineBankCodec.encode T).length
  have hw (j : Fin 32) : (bank ι S T j).length ≤ n + m := by
    by_cases hj : ∃ i : Fin 12, ι i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [bank_at]
      have h := BitMachineBankCodec.word_length_le_encode T i
      omega
    · rw [bank_outside ι S T j hj]
      have h := BitMachineBankCodec.word_length_le_encode S j
      omega
  have hs : (∑ j : Fin 32, (bank ι S T j).length) ≤
      ∑ _j : Fin 32, (n + m) :=
    Finset.sum_le_sum (by intro j _; exact hw j)
  rw [BitMachineBankCodec.encode_length]
  simp at hs
  omega

private theorem embedded9_size (ι : Fin 9 ↪ Fin 32) (S : Bank)
    (T : Fin 9 → List Bool) :
    (BitMachineBankCodec.encode (bank ι S T)).length ≤
      65 * ((BitMachineBankCodec.encode S).length +
        (BitMachineBankCodec.encode T).length + 1) := by
  let n := (BitMachineBankCodec.encode S).length
  let m := (BitMachineBankCodec.encode T).length
  have hw (j : Fin 32) : (bank ι S T j).length ≤ n + m := by
    by_cases hj : ∃ i : Fin 9, ι i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [bank_at]
      have h := BitMachineBankCodec.word_length_le_encode T i
      omega
    · rw [bank_outside ι S T j hj]
      have h := BitMachineBankCodec.word_length_le_encode S j
      omega
  have hs : (∑ j : Fin 32, (bank ι S T j).length) ≤
      ∑ _j : Fin 32, (n + m) :=
    Finset.sum_le_sum (by intro j _; exact hw j)
  rw [BitMachineBankCodec.encode_length]
  simp at hs
  omega

theorem cross_size (S : Bank) :
    (BitMachineBankCodec.encode (crossBank S)).length ≤
      34000 * ((BitMachineBankCodec.encode S).length + 1) := by
  have hr := restricted12_size crossSlots S
  have hp := RationalProductPacket.size_bound (restricted crossSlots S)
  have he := embedded12_size crossSlots S
    (RationalProductPacket.resultBank (restricted crossSlots S))
  change (BitMachineBankCodec.encode (crossBank S)).length ≤
    65 * ((BitMachineBankCodec.encode S).length +
      (BitMachineBankCodec.encode (RationalProductPacket.resultBank
        (restricted crossSlots S))).length + 1) at he
  omega

theorem den_size (S : Bank) :
    (BitMachineBankCodec.encode (denBank S)).length ≤
      34000 * ((BitMachineBankCodec.encode S).length + 1) := by
  have hr := restricted12_size denSlots S
  have hp := RationalProductPacket.size_bound (restricted denSlots S)
  have he := embedded12_size denSlots S
    (RationalProductPacket.resultBank (restricted denSlots S))
  change (BitMachineBankCodec.encode (denBank S)).length ≤
    65 * ((BitMachineBankCodec.encode S).length +
      (BitMachineBankCodec.encode (RationalProductPacket.resultBank
        (restricted denSlots S))).length + 1) at he
  omega

theorem product_size (S : Bank) :
    (BitMachineBankCodec.encode (productBank S)).length ≤
      1200000000 * ((BitMachineBankCodec.encode S).length + 1) := by
  have h₁ := cross_size S
  have h₂ := den_size (crossBank S)
  dsimp only [productBank]
  omega

theorem final_size (S : Bank) :
    (BitMachineBankCodec.encode (finalBank S)).length ≤
      150000000000000 * ((BitMachineBankCodec.encode S).length + 1) := by
  have hp := product_size S
  have hr := restricted9_size subSlots (productBank S)
  change (BitMachineBankCodec.encode (subInput (productBank S))).length ≤
    19 * ((BitMachineBankCodec.encode (productBank S)).length + 1) at hr
  have hs := SignedMagnitudeSubtract.size_bound (subInput (productBank S))
  have he := embedded9_size subSlots (productBank S)
    (SignedMagnitudeSubtract.finalBank (subInput (productBank S)))
  change (BitMachineBankCodec.encode (finalBank S)).length ≤
    65 * ((BitMachineBankCodec.encode (productBank S)).length +
      (BitMachineBankCodec.encode (SignedMagnitudeSubtract.finalBank
        (subInput (productBank S)))).length + 1) at he
  omega

theorem local_time_bound (S : Bank) :
    RationalProductPacket.clearTime (restricted crossSlots S) +
      RationalProductPacket.rawTime (restricted crossSlots S) +
      RationalProductPacket.clearTime (restricted denSlots (crossBank S)) +
      RationalProductPacket.rawTime (restricted denSlots (crossBank S)) +
      SignedMagnitudeSubtract.localTime (subInput (productBank S)) + 2 ≤
      100000000000000 * ((BitMachineBankCodec.encode S).length + 1)^2 := by
  let n := (BitMachineBankCodec.encode S).length
  have hcr := restricted12_size crossSlots S
  have hct := RationalProductPacket.time_bound (restricted crossSlots S)
  have hcs := cross_size S
  have hdr := restricted12_size denSlots (crossBank S)
  have hdt := RationalProductPacket.time_bound (restricted denSlots (crossBank S))
  have hps := product_size S
  have hsr := restricted9_size subSlots (productBank S)
  change (BitMachineBankCodec.encode (subInput (productBank S))).length ≤
    19 * ((BitMachineBankCodec.encode (productBank S)).length + 1) at hsr
  have hst := SignedMagnitudeSubtract.time_bound (subInput (productBank S))
  have hn : 1 ≤ n + 1 := by omega
  have hn2 : n + 1 ≤ (n + 1)^2 := by nlinarith
  have hca : (BitMachineBankCodec.encode (restricted crossSlots S)).length + 1 ≤
      26*(n+1) := by omega
  have hda : (BitMachineBankCodec.encode
      (restricted denSlots (crossBank S))).length + 1 ≤
      850026*(n+1) := by omega
  have hsa : (BitMachineBankCodec.encode
      (subInput (productBank S))).length + 1 ≤
      22800000020*(n+1) := by omega
  have hct' : RationalProductPacket.clearTime (restricted crossSlots S) +
      RationalProductPacket.rawTime (restricted crossSlots S) ≤
      67600*(n+1)^2 := by
    calc
      _ ≤ 100*((BitMachineBankCodec.encode
        (restricted crossSlots S)).length+1)^2 := hct
      _ ≤ 100*(26*(n+1))^2 := by gcongr
      _ = 67600*(n+1)^2 := by ring
  have hdt' : RationalProductPacket.clearTime
      (restricted denSlots (crossBank S)) +
      RationalProductPacket.rawTime (restricted denSlots (crossBank S)) ≤
      72254420067600*(n+1)^2 := by
    calc
      _ ≤ 100*((BitMachineBankCodec.encode
        (restricted denSlots (crossBank S))).length+1)^2 := hdt
      _ ≤ 100*(850026*(n+1))^2 := by gcongr
      _ = 72254420067600*(n+1)^2 := by ring
  have hst' : SignedMagnitudeSubtract.localTime (subInput (productBank S)) ≤
      342000000300*(n+1)^2 := by
    calc
      _ ≤ 15*((BitMachineBankCodec.encode
        (subInput (productBank S))).length+1) := hst
      _ ≤ 15*(22800000020*(n+1)) := Nat.mul_le_mul_left _ hsa
      _ ≤ 342000000300*(n+1)^2 := by nlinarith
  change RationalProductPacket.clearTime (restricted crossSlots S) +
      RationalProductPacket.rawTime (restricted crossSlots S) +
      RationalProductPacket.clearTime (restricted denSlots (crossBank S)) +
      RationalProductPacket.rawTime (restricted denSlots (crossBank S)) +
      SignedMagnitudeSubtract.localTime (subInput (productBank S)) + 2 ≤
      100000000000000*(n+1)^2
  omega

noncomputable def machine : BitMachine.Machine :=
  BitMachineBankWrapper.machine program start initial

noncomputable def result (input : List Bool) : List Bool :=
  BitMachineBankWrapper.result finalBank input

theorem polytime : BitMachine.Polytime result := by
  apply BitMachineBankWrapper.polytime program start initial finalBank
    100000000000000 2 150000000000000 1
  · intro S
    obtain ⟨t, ht, hr⟩ := RationalSubtractCore.local_run S
    refine ⟨t, ⟨none, initial, finalBank S⟩,
      ht.trans (local_time_bound S), hr, rfl, rfl⟩
  · intro S
    simpa only [pow_one] using final_size S

end EthInapproximability.CurrentPaper.RationalSubtractClock
