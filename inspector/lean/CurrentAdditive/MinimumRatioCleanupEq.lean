import CurrentAdditive.MinimumRatioExtraClear

namespace CurrentAdditive.MinimumRatioCleanupEq

open EthInapproximability.CurrentPaper
open CurrentAdditive.MinimumRatioCallbackLayout

private theorem outside_low (k : Stack)
    (hk : ¬∃ i : Fin 17, CurrentAdditive.MinimumRatioExtraClear.extraBank i = k)
    (j : Fin 32) (hj : 15 ≤ j.val) : k ≠ low j := by
  intro he
  obtain ⟨i, hi⟩ := CurrentAdditive.MinimumRatioExtraClear.covered j hj
  exact hk ⟨i, hi.trans he.symm⟩

theorem item_cleanup_eq (S : Bank) (word best : List Bool)
    (h9 : S (low 9) = best)
    (hscratch : CurrentAdditive.MinimumRatioCallbackFull.ScratchEmpty S) :
    let pos := MinimumRatioPositiveMachine.result word
    let q := RationalCanonicalCallback.quotientResult word
    let pair := RawRatPairAssembler.pairWord q best.tail
    let S2 := Function.update
      (Function.update
        (Function.update S (low 15) pos) (low 16) q)
      (low 20) best.tail
    let S3 := Function.update
      (Function.update S2 (low 26) pair)
      (low 18) (RationalLess.result pair)
    let U := Function.update
      (CurrentAdditive.MinimumRatioBestUpdate.readBank S3)
      (low 9) (CurrentAdditive.MinimumRatioBestUpdate.chosenBest S3)
    BitMachineClearBank.cleared
      CurrentAdditive.MinimumRatioExtraClear.extraBank U =
      Function.update S (low 9)
        (CurrentAdditive.MinimumRatioStepSpec.step best word) := by
  dsimp only
  let pos := MinimumRatioPositiveMachine.result word
  let q := RationalCanonicalCallback.quotientResult word
  let pair := RawRatPairAssembler.pairWord q best.tail
  let S2 := Function.update
    (Function.update
      (Function.update S (low 15) pos) (low 16) q)
    (low 20) best.tail
  let S3 := Function.update
    (Function.update S2 (low 26) pair)
    (low 18) (RationalLess.result pair)
  let U := Function.update
    (CurrentAdditive.MinimumRatioBestUpdate.readBank S3)
    (low 9) (CurrentAdditive.MinimumRatioBestUpdate.chosenBest S3)
  have hchosen : CurrentAdditive.MinimumRatioBestUpdate.chosenBest S3 =
      CurrentAdditive.MinimumRatioStepSpec.step best word := by
    simpa [S3, S2, pos, q, pair] using
      CurrentAdditive.MinimumRatioStepPhysicalBridge.phased_chosen_best
        S word best h9
  apply CurrentAdditive.MinimumRatioExtraClear.cleaned_eq S U
    (CurrentAdditive.MinimumRatioStepSpec.step best word) hscratch
  intro k hk
  have h15 := outside_low k hk 15 (by decide)
  have h16 := outside_low k hk 16 (by decide)
  have h18 := outside_low k hk 18 (by decide)
  have h20 := outside_low k hk 20 (by decide)
  have h26 := outside_low k hk 26 (by decide)
  by_cases h9k : k = low 9
  · subst k
    simp [U, hchosen]
  · simp [U, S3, S2, CurrentAdditive.MinimumRatioBestUpdate.readBank,
      Function.update_of_ne, h9k, h15, h16, h18, h20, h26, hchosen]

end CurrentAdditive.MinimumRatioCleanupEq
