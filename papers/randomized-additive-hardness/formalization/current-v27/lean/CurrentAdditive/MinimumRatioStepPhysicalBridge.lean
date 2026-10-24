import CurrentAdditive.MinimumRatioCallbackFull

namespace CurrentAdditive.MinimumRatioStepPhysicalBridge

open EthInapproximability.CurrentPaper
open CurrentAdditive.MinimumRatioCallbackLayout

theorem positive_shape (word : List Bool) :
    MinimumRatioPositiveMachine.result word = [] ∨
      MinimumRatioPositiveMachine.result word = [true] := by
  unfold MinimumRatioPositiveMachine.result
  split <;> try simp
  split <;> try simp
  tauto

theorem less_shape (word : List Bool) :
    RationalLess.result word = [] ∨ RationalLess.result word = [true] := by
  unfold RationalLess.result RationalStrictNegative.result
  split <;> try simp
  tauto

theorem chosen_best_eq_step (S : Bank) (word best : List Bool)
    (hpos : S (low 15) = MinimumRatioPositiveMachine.result word)
    (hbest : S (low 9) = best)
    (hq : S (low 16) = RationalCanonicalCallback.quotientResult word)
    (hless : S (low 18) = RationalLess.result
      (RawRatPairAssembler.pairWord
        (RationalCanonicalCallback.quotientResult word) best.tail)) :
    CurrentAdditive.MinimumRatioBestUpdate.chosenBest S =
      CurrentAdditive.MinimumRatioStepSpec.step best word := by
  rcases positive_shape word with hp | hp <;>
    rcases less_shape (RawRatPairAssembler.pairWord
      (RationalCanonicalCallback.quotientResult word) best.tail) with hl | hl
  all_goals
    cases best with
    | nil =>
        simp [CurrentAdditive.MinimumRatioBestUpdate.chosenBest,
          CurrentAdditive.MinimumRatioBestUpdate.shouldReplace,
          CurrentAdditive.MinimumRatioStepSpec.step,
          hpos, hbest, hq, hless, hp, hl]
    | cons b bs =>
        simp only [List.tail_cons] at hless hl
        simp [CurrentAdditive.MinimumRatioBestUpdate.chosenBest,
          CurrentAdditive.MinimumRatioBestUpdate.shouldReplace,
          CurrentAdditive.MinimumRatioStepSpec.step,
          hpos, hbest, hq, hless, hp, hl]

theorem phased_chosen_best (S : Bank) (word best : List Bool)
    (h9 : S (low 9) = best) :
    let pos := MinimumRatioPositiveMachine.result word
    let q := RationalCanonicalCallback.quotientResult word
    let pair := RawRatPairAssembler.pairWord q best.tail
    let S3 := Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update S (low 15) pos) (low 16) q)
          (low 20) best.tail)
        (low 26) pair)
      (low 18) (RationalLess.result pair)
    CurrentAdditive.MinimumRatioBestUpdate.chosenBest S3 =
      CurrentAdditive.MinimumRatioStepSpec.step best word := by
  dsimp only
  let pos := MinimumRatioPositiveMachine.result word
  let q := RationalCanonicalCallback.quotientResult word
  let pair := RawRatPairAssembler.pairWord q best.tail
  let S3 := Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update S (low 15) pos) (low 16) q)
          (low 20) best.tail)
        (low 26) pair)
      (low 18) (RationalLess.result pair)
  have hp : S3 (low 15) = pos := by
    simp [S3, CurrentAdditive.MinimumRatioCallbackFull.at_other]
  have hb : S3 (low 9) = best := by
    simp [S3, CurrentAdditive.MinimumRatioCallbackFull.at_other, h9]
  have hq : S3 (low 16) = q := by
    simp [S3, CurrentAdditive.MinimumRatioCallbackFull.at_other]
  have hl : S3 (low 18) = RationalLess.result pair := by simp [S3]
  exact chosen_best_eq_step S3 word best
    (by simpa [pos] using hp) hb
    (by simpa [q] using hq)
    (by simpa [q, pair] using hl)

end CurrentAdditive.MinimumRatioStepPhysicalBridge
