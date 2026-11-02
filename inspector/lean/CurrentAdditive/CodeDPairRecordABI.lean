import CurrentAdditive.CodeDTargetV2
import CurrentAdditive.CodeDSourceBank2Field15
import CurrentAdditive.CodeDAlphabetBank2Field15
import CurrentAdditive.CodeDPairWeights15

/-! The two canonical entry codecs use the same literal Bank2 framing.
Their second fields are exactly the RawRat bytes consumed by the pair
request serializer. -/

namespace CurrentAdditive.CodeDPairRecordABI

open EthInapproximability.CurrentPaper.BitMachineBankCodec
open CurrentAdditive.CodeDCodec
open CurrentAdditive.CodeDSourceCodecV2
open CurrentAdditive.CodeDCanonicalSourceV2

def sourceBank (x : Entry) : Bank 2 :=
  fun i => if i = 0 then CurrentAdditive.CodeDCodecV2.encodeItems x.word
    else encodeRawRat x.weight

def alphabetBank (y : Nat × ℚ) : Bank 2 :=
  fun i => if i = 0 then y.1.bits else encodeRawRat (rawOfRat y.2)

theorem source_record (x : Entry) : encode (sourceBank x) = encodeEntry x := by
  rfl

theorem alphabet_record (y : Nat × ℚ) :
    encode (alphabetBank y) = CurrentAdditive.CodeDTargetV2.alphabetEntry y := by
  rfl

@[simp] theorem source_weight (x : Entry) :
    sourceBank x 1 = encodeRawRat x.weight := by
  rfl

@[simp] theorem alphabet_weight (y : Nat × ℚ) :
    alphabetBank y 1 = encodeRawRat (rawOfRat y.2) := by
  rfl

theorem request_bytes (x : Entry) (y : Nat × ℚ) :
    CurrentAdditive.CodeDPairWeights15.pairBank x.weight (rawOfRat y.2) 0 =
      sourceBank x 1 ∧
    CurrentAdditive.CodeDPairWeights15.pairBank x.weight (rawOfRat y.2) 1 =
      alphabetBank y 1 := by
  exact ⟨rfl, rfl⟩

#print axioms request_bytes

end CurrentAdditive.CodeDPairRecordABI
