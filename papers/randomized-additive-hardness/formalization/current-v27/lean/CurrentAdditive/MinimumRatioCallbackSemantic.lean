import CurrentAdditive.MinimumRatioCallbackPhysical

/-! The physical one-item callback has the intended minimum-ratio action on
canonical rational pairs.  Iterating this callback over the ordered
certificate list is a separate controller obligation. -/

namespace CurrentAdditive.MinimumRatioCallbackSemantic

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioCallbackLayout

theorem callback_pair {weight coeff : CurrentAdditive.CodeDCodec.RawRat}
    (S : Bank) (best : Option ℚ)
    (hw : weight.Valid) (hc : coeff.Valid)
    (h6 : S (low 6) =
      CurrentAdditive.CodeDPairProductTargetV2.pairBytes weight coeff)
    (h9 : S (low 9) = CurrentAdditive.MinimumRatioStepSpec.bestPacket best)
    (hscratch : CurrentAdditive.MinimumRatioCallbackFull.ScratchEmpty S) :
    ∃ u ≤ MinimumRatioCallbackPhysical.itemClock S
          (CurrentAdditive.CodeDPairProductTargetV2.pairBytes weight coeff)
          (CurrentAdditive.MinimumRatioStepSpec.bestPacket best) +
        (∑ j : Fin 17,
          ((MinimumRatioCallbackPhysical.postItemBank S
            (CurrentAdditive.CodeDPairProductTargetV2.pairBytes weight coeff)
            (CurrentAdditive.MinimumRatioStepSpec.bestPacket best))
            (CurrentAdditive.MinimumRatioExtraClear.extraBank j)).length) + 20,
      ((advance MinimumRatioCallbackPhysical.program)^[u])
        (⟨some MinimumRatioCallbackPhysical.start,
          MinimumRatioCallbackPhysical.control, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, MinimumRatioCallbackPhysical.control,
          Function.update S (low 9)
            (CurrentAdditive.MinimumRatioStepSpec.bestPacket
              (CurrentAdditive.MinimumRatioStepSpec.semanticStep best
                weight.value coeff.value))⟩ := by
  obtain ⟨u, hu, hr⟩ :=
    MinimumRatioCallbackPhysical.callback_run S
      (CurrentAdditive.CodeDPairProductTargetV2.pairBytes weight coeff)
      (CurrentAdditive.MinimumRatioStepSpec.bestPacket best)
      h6 h9 hscratch
  refine ⟨u, hu, ?_⟩
  rw [CurrentAdditive.MinimumRatioStepSpec.step_pair best weight coeff hw hc] at hr
  exact hr

#print axioms callback_pair

end CurrentAdditive.MinimumRatioCallbackSemantic
