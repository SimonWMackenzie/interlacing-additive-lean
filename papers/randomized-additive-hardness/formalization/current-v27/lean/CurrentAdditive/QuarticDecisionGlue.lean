import CurrentAdditive.QuarticDecisionStage

/-! The tape cutter, formula core, and estimator are composed as one fixed machine. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open EthInapproximability.CurrentPaper
open Paper2

noncomputable def sourceDecision27 (tail : BitMachine.Machine)
    (C : Paper2.SelectedTape.Algorithm) (K N₁ : ℕ) : BitMachine.Machine :=
  BitMachineComposition.composition (Paper2.AEth5.twoCut K N₁ C.cR)
    (BitMachineComposition.composition
      (Paper2.Unit4Shell.PairMap.machine (sourceCore27 tail))
      (Paper2.AEth5.clsStage C))

noncomputable def sourceDecisionClock27
    (C : Paper2.SelectedTape.Algorithm) (x f raw block w : List Bool)
    (Ttwo Tcore Y : ℕ) : ℕ :=
  let To := 2 * (EncodedComplexity.pair f raw).length + Tcore + 2 * w.length + 6
  Ttwo + 2 * (EncodedComplexity.pair
      (EncodedComplexity.pair f raw) block).length + 2 +
    To + 2 * (EncodedComplexity.pair w block).length + 2 +
    Paper2.AEth5.clsTime C w.length Y

theorem sourceDecision27_outputs_of_components
    (tail : BitMachine.Machine) (C : Paper2.SelectedTape.Algorithm)
    (K N₁ : ℕ) (x tape f raw block w : List Bool)
    (Ttwo Tcore Y : ℕ)
    (htwo : (Paper2.AEth5.twoCut K N₁ C.cR).OutputsWithin
      (EncodedComplexity.pair x tape)
      (EncodedComplexity.pair (EncodedComplexity.pair f raw) block) Ttwo)
    (hcore : (sourceCore27 tail).OutputsWithin
      (EncodedComplexity.pair f raw) w Tcore)
    (hY : block.length ≤ Y)
    (hfit : C.tapeLength w ≤ block.length) :
    (sourceDecision27 tail C K N₁).OutputsWithin
      (EncodedComplexity.pair x tape)
      (C.output w (block.take (C.tapeLength w)))
      (sourceDecisionClock27 C x f raw block w Ttwo Tcore Y) := by
  have houter := Paper2.Unit4Shell.PairMap.machine_outputs
    (M := sourceCore27 tail) (EncodedComplexity.pair f raw) w block _ hcore
  have hcls := Paper2.AEth5.clsStage_outputs C w block Y hY hfit
  have hsecond := BitMachineComposition.composition_outputsWithin
    (Paper2.Unit4Shell.PairMap.machine (sourceCore27 tail))
    (Paper2.AEth5.clsStage C) houter hcls
  have hfull := BitMachineComposition.composition_outputsWithin
    (Paper2.AEth5.twoCut K N₁ C.cR)
    (BitMachineComposition.composition
      (Paper2.Unit4Shell.PairMap.machine (sourceCore27 tail))
      (Paper2.AEth5.clsStage C)) htwo hsecond
  change (BitMachineComposition.composition (Paper2.AEth5.twoCut K N₁ C.cR)
    (BitMachineComposition.composition
      (Paper2.Unit4Shell.PairMap.machine (sourceCore27 tail))
      (Paper2.AEth5.clsStage C))).OutputsWithin _ _ _
  apply BitMachine.outputsWithin_mono _ hfull
  dsimp only [sourceDecisionClock27]
  omega

#print axioms sourceDecision27_outputs_of_components

end Paper2.CurrentAdditive.QuarticClassEndpoint
