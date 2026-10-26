import CurrentAdditive.MinimumRatioPositiveRun
import CurrentAdditive.RationalCanonicalCallback
import CurrentAdditive.RationalLess
import CurrentAdditive.RawRatPairAssembler
import Mathlib.Tactic

/-! Total byte-level step specification for the physical minimum-ratio callback.
No execution theorem is asserted here; each constituent machine is separately
physical and the stateful composition is a later obligation. -/

namespace CurrentAdditive.MinimumRatioStepSpec

open EthInapproximability.CurrentPaper
open CurrentAdditive.CodeDCodec

def bestPacket : Option ℚ → List Bool
  | none => []
  | some q => true :: encodeRawRat (CodeDCanonicalSource.rawOfRat q)

noncomputable def step (best word : List Bool) : List Bool :=
  if MinimumRatioPositiveMachine.result word = [true] then
    let candidate := RationalCanonicalCallback.quotientResult word
    if best.isEmpty then true :: candidate
    else if RationalLess.result
      (RawRatPairAssembler.pairWord candidate best.tail) = [true] then
      true :: candidate
    else best
  else best

def semanticStep (best : Option ℚ) (weight coeff : ℚ) : Option ℚ :=
  if 0 < coeff then
    let ratio := weight / coeff
    match best with
    | none => some ratio
    | some old => if ratio < old then some ratio else some old
  else best

private theorem numerator_pos_of_value_pos (r : RawRat)
    (hr : r.Valid) (hp : 0 < r.value) :
    0 < EncodedCommunication.bitsValue r.numerator := by
  have hb := (MinimumRatioPositiveRun.coeff_positive_iff r hr).1 hp
  have hn : r.numerator.any id = true := by
    cases hs : r.negative <;> simp [hs] at hb ⊢
    exact hb
  have hz := BitMachineBinaryZeroTest.any_false_iff_value_zero r.numerator
  by_contra h
  have h0 : EncodedCommunication.bitsValue r.numerator = 0 := by omega
  have hf := hz.mpr h0
  simp [hf] at hn

theorem step_pair (best : Option ℚ) (weight coeff : RawRat)
    (hw : weight.Valid) (hc : coeff.Valid) :
    step (bestPacket best)
      (CodeDPairProductTargetV2.pairBytes weight coeff) =
    bestPacket (semanticStep best weight.value coeff.value) := by
  by_cases hp : 0 < coeff.value
  · have hpos := MinimumRatioPositiveRun.result_pair_positive weight coeff hc
    rw [if_pos hp] at hpos
    have hnum := numerator_pos_of_value_pos coeff hc hp
    have hquot := RationalCanonicalCallback.quotient_result_pair
      weight coeff hw hc hnum
    cases best with
    | none =>
        simp [step, bestPacket, semanticStep, hp, hpos, hquot]
    | some old =>
        have hpair := RawRatPairAssembler.pairWord_exact
          (CodeDCanonicalSource.rawOfRat (weight.value / coeff.value))
          (CodeDCanonicalSource.rawOfRat old)
        have hless := RationalLess.result_pair
          (CodeDCanonicalSource.rawOfRat (weight.value / coeff.value))
          (CodeDCanonicalSource.rawOfRat old)
          (CodeDCanonicalSource.rawOfRat_valid _)
          (CodeDCanonicalSource.rawOfRat_valid _)
        rw [CodeDCanonicalSource.rawOfRat_value,
          CodeDCanonicalSource.rawOfRat_value] at hless
        by_cases hlt : weight.value / coeff.value < old
        · rw [if_pos hlt] at hless
          simp [step, bestPacket, semanticStep, hp, hpos, hquot,
            hpair, hless, hlt]
        · rw [if_neg hlt] at hless
          simp [step, bestPacket, semanticStep, hp, hpos, hquot,
            hpair, hless, hlt]
  · have hpos := MinimumRatioPositiveRun.result_pair_positive weight coeff hc
    rw [if_neg hp] at hpos
    simp [step, semanticStep, hp, hpos]

#print axioms step_pair

end CurrentAdditive.MinimumRatioStepSpec
