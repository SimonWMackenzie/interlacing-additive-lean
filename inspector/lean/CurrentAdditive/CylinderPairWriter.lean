import CurrentAdditive.CylinderFeatureCodec
import EthInapproximability.CurrentPaper.BitMachineBankSerialize

/-! Literal physical writer for a variable-size cylinder assignment pair.
The source coordinate and alphabet symbol are separate prepared bit stacks;
the fixed Bank2 serializer consumes both and writes the exact ABI record. -/

namespace CurrentAdditive.CylinderPairWriter

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open CurrentAdditive.CylinderFeatureCodec

theorem serializer_bytes (p : Nat × Nat) :
    BitMachineBankSerialize.encode (List.ofFn (pairBank p)) = encodePair p := by
  exact (encode_eq_list (pairBank p)).symm

theorem physical_pair (p : Nat × Nat) (source oldOutput : List Bool) :
    ∃ (t : Nat) (remaining : BitMachineBankSerialize.Bank 2),
      t ≤ 2 * (encodePair p).length + 2 ∧
      BitMachineBankSerialize.run t
        (BitMachineBankSerialize.cfg (some (.emit 0)) none
          (pairBank p) source [] oldOutput) =
        BitMachineBankSerialize.cfg none none remaining source []
          (encodePair p ++ oldOutput) := by
  obtain ⟨t, remaining, ht, hr⟩ :=
    BitMachineBankSerialize.serialize (pairBank p) source oldOutput
  refine ⟨t, remaining, ?_, ?_⟩
  · simpa only [serializer_bytes] using ht
  · simpa only [serializer_bytes] using hr

theorem pair_length (p : Nat × Nat) :
    (encodePair p).length = 2 * (p.1.bits.length + p.2.bits.length) + 2 := by
  rw [encodePair, encode_length]
  simp [pairBank, Fin.sum_univ_two]

#print axioms physical_pair

end CurrentAdditive.CylinderPairWriter
