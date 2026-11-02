import CurrentAdditive.QuarticPrinterFixedClock

/-! The fixed v27 decision skeleton runs on every input word, including
malformed words, after routing to a valid formula. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open EthInapproximability.CurrentPaper
open Paper2

theorem sourceDecision_any27 (tail : BitMachine.Machine)
    (C : Paper2.SelectedTape.Algorithm) (K N₁ : ℕ)
    (hN₁ : 1 ≤ N₁) (x tape w : List Bool) (Ttail Y : ℕ) :
    let Φ := Paper2.AEth4.routed4 K N₁ x
    let raw := tape.take (Paper2.AEth3.cutLen Φ)
    let block := (tape.take (2 ^ C.cR * Paper2.AEth3.cutLen Φ)).drop
      (Paper2.AEth3.cutLen Φ)
    tail.OutputsWithin
      (EncodedComplexity.pair (EncodedCNF.encode Φ) raw) w Ttail →
    block.length ≤ Y →
    C.tapeLength w ≤ block.length →
    (sourceDecision27 tail C K N₁).OutputsWithin
      (EncodedComplexity.pair x tape)
      (C.output w (block.take (C.tapeLength w)))
      (sourceDecisionClock27 C x (Paper2.AEth3.fOut Φ)
        raw block w
        (Paper2.AEth5.twoCutTime K N₁ C.cR x)
        (sourceCoreClock27 Φ raw Ttail) Y) := by
  intro Φ raw block htail hY hfit
  have htwo := Paper2.AEth5.twoCut_outputs K N₁ C.cR hN₁ x tape
  have hL : Paper2.AEth5.L1 K N₁ x = Paper2.AEth3.cutLen Φ := rfl
  rw [hL] at htwo
  have hcore := sourceCore27_outputs tail Φ raw w Ttail htail
  exact sourceDecision27_outputs_of_components tail C K N₁
    x tape (Paper2.AEth3.fOut Φ) raw block w
    (Paper2.AEth5.twoCutTime K N₁ C.cR x)
    (sourceCoreClock27 Φ raw Ttail) Y htwo hcore hY hfit

#print axioms sourceDecision_any27

end Paper2.CurrentAdditive.QuarticClassEndpoint
