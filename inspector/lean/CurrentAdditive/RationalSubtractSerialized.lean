import CurrentAdditive.RationalSubtractSelect3
import Mathlib.Tactic

/-! The fixed 32-bank subtraction output is physically serialized as RawRat bytes. -/

namespace EthInapproximability.CurrentPaper.RationalSubtractSerialized

open CurrentAdditive.CodeDCodec
open RationalSubtractCore

abbrev Bank := RationalSubtractCore.Bank

noncomputable def result : List Bool → List Bool :=
  RationalSubtractSelect3.result ∘ RationalSubtractDenReverse.result ∘
    RationalSubtractPairMachine.totalResult

theorem polytime : BitMachine.Polytime result := by
  have h := BitMachineComposition.polytime_comp
    RationalSubtractPairMachine.total_polytime
    RationalSubtractDenReverse.polytime
  simpa only [result, Function.comp_assoc] using
    BitMachineComposition.polytime_comp h RationalSubtractSelect3.polytime

private theorem sign_shape (a b : RawRat) :
    ∃ neg : Bool,
      finalBank (RationalSubtractSpec.canonicalBank a b) 30 =
        if neg then [true] else [] := by
  let S := productBank (RationalSubtractSpec.canonicalBank a b)
  let T := subInput S
  let w := SignedMagnitudeSubtract.scanWords (T 2) (T 3)
    false false false
  let s := SignedMagnitudeSubtract.scanState
    ((T 0).head?.getD false) ((T 1).head?.getD false)
    w.borrowAB w.borrowBA w.carry
  refine ⟨SignedMagnitudeSubtract.outputNegative s, ?_⟩
  have h7 : T 7 = [] := by
    dsimp only [T, S]
    rw [RationalSubtractSpec.sub_input_canonical]
    rfl
  have h := BitMachineStackEmbedding.bank_at subSlots S
    (SignedMagnitudeSubtract.finalBank T) 7
  change finalBank (RationalSubtractSpec.canonicalBank a b) 30 =
    SignedMagnitudeSubtract.finalBank T 7 at h
  rw [h]
  simp [SignedMagnitudeSubtract.finalBank,
    SignedMagnitudeSubtract.contents, h7, w, s]

theorem sign_word (a b : RawRat) :
    finalBank (RationalSubtractSpec.canonicalBank a b) 30 =
      if (RationalSubtractSpec.outputRat a b).negative
      then [true] else [] := by
  obtain ⟨neg, hs⟩ := sign_shape a b
  have hn : (RationalSubtractSpec.outputRat a b).negative = neg := by
    cases neg <;> simp [RationalSubtractSpec.outputRat, hs]
  simpa only [hn] using hs

theorem selected_eq_rawRatBank (a b : RawRat) :
    RationalSubtractSelect3.selected
      (RationalSubtractDenReverse.reversedBank
        (finalBank (RationalSubtractSpec.canonicalBank a b))) =
      rawRatBank (RationalSubtractSpec.outputRat a b) := by
  funext i
  fin_cases i
  · simp [RationalSubtractSelect3.selected,
      RationalSubtractSelect3.serIndex,
      RationalSubtractDenReverse.reversedBank,
      BitMachineBroadcast.contents,
      RationalSubtractDenReverse.cleared,
      rawRatBank, sign_word]
  · simp [RationalSubtractSelect3.selected,
      RationalSubtractSelect3.serIndex,
      RationalSubtractDenReverse.reversedBank,
      BitMachineBroadcast.contents,
      RationalSubtractDenReverse.cleared,
      rawRatBank, RationalSubtractSpec.outputRat]
  · simp [RationalSubtractSelect3.selected,
      RationalSubtractSelect3.serIndex,
      RationalSubtractDenReverse.reversedBank,
      BitMachineBroadcast.contents,
      RationalSubtractDenReverse.cleared,
      rawRatBank, RationalSubtractSpec.outputRat]

theorem result_pair (a b : RawRat) :
    result (RationalSubtractPairMachine.pairBytes a b) =
      encodeRawRat (RationalSubtractSpec.outputRat a b) := by
  rw [result, Function.comp_apply, Function.comp_apply,
    RationalSubtractPairMachine.total_result_pair,
    RationalSubtractSpec.canonical_result,
    RationalSubtractDenReverse.result_encode,
    RationalSubtractSelect3.result_encode,
    selected_eq_rawRatBank]
  rfl

#print axioms polytime
#print axioms result_pair

end EthInapproximability.CurrentPaper.RationalSubtractSerialized
