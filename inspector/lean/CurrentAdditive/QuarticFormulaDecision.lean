import CurrentAdditive.QuarticFormulaCut

/-! A formula and fair tape run through the fixed v27 decision skeleton. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open EthInapproximability.CurrentPaper
open Paper2

theorem sourceDecision_formula27 (tail : BitMachine.Machine)
    (C : Paper2.SelectedTape.Algorithm) (K N₁ : ℕ)
    (hN₁ : 1 ≤ N₁) (Φ : EncodedCNF.Formula)
    (hroute : Paper2.AEth4.routed4 K N₁ (EncodedCNF.encode Φ) = Φ)
    (tape w : List Bool) (Ttail Y : ℕ)
    (htail : tail.OutputsWithin
      (EncodedComplexity.pair (EncodedCNF.encode Φ)
        (tape.take (Paper2.AEth3.cutLen Φ))) w Ttail)
    (hY : ((tape.take (2 ^ C.cR * Paper2.AEth3.cutLen Φ)).drop
      (Paper2.AEth3.cutLen Φ)).length ≤ Y)
    (hfit : C.tapeLength w ≤
      ((tape.take (2 ^ C.cR * Paper2.AEth3.cutLen Φ)).drop
        (Paper2.AEth3.cutLen Φ)).length) :
    let raw := tape.take (Paper2.AEth3.cutLen Φ)
    let block := (tape.take (2 ^ C.cR * Paper2.AEth3.cutLen Φ)).drop
      (Paper2.AEth3.cutLen Φ)
    (sourceDecision27 tail C K N₁).OutputsWithin
      (EncodedComplexity.pair (EncodedCNF.encode Φ) tape)
      (C.output w (block.take (C.tapeLength w)))
      (sourceDecisionClock27 C (EncodedCNF.encode Φ) (Paper2.AEth3.fOut Φ)
        raw block w
        (Paper2.AEth5.twoCutTime K N₁ C.cR (EncodedCNF.encode Φ))
        (sourceCoreClock27 Φ raw Ttail) Y) := by
  intro raw block
  have htwo := twoCut_formula27 C K N₁ hN₁ Φ hroute tape
  have hcore := sourceCore27_outputs tail Φ raw w Ttail htail
  exact sourceDecision27_outputs_of_components tail C K N₁
    (EncodedCNF.encode Φ) tape (Paper2.AEth3.fOut Φ) raw block w
    (Paper2.AEth5.twoCutTime K N₁ C.cR (EncodedCNF.encode Φ))
    (sourceCoreClock27 Φ raw Ttail) Y htwo hcore hY hfit

#print axioms sourceDecision_formula27

end Paper2.CurrentAdditive.QuarticClassEndpoint
