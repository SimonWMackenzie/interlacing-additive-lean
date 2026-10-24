import CurrentAdditive.QuarticDecisionGlue

/-! The inherited cutter routes a source formula into a fixed prefix and block. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open EthInapproximability.CurrentPaper
open Paper2

theorem twoCut_formula27 (C : Paper2.SelectedTape.Algorithm)
    (K N₁ : ℕ) (hN₁ : 1 ≤ N₁) (Φ : EncodedCNF.Formula)
    (hroute : Paper2.AEth4.routed4 K N₁ (EncodedCNF.encode Φ) = Φ)
    (tape : List Bool) :
    (Paper2.AEth5.twoCut K N₁ C.cR).OutputsWithin
      (EncodedComplexity.pair (EncodedCNF.encode Φ) tape)
      (EncodedComplexity.pair
        (EncodedComplexity.pair (Paper2.AEth3.fOut Φ)
          (tape.take (Paper2.AEth3.cutLen Φ)))
        ((tape.take (2 ^ C.cR * Paper2.AEth3.cutLen Φ)).drop
          (Paper2.AEth3.cutLen Φ)))
      (Paper2.AEth5.twoCutTime K N₁ C.cR (EncodedCNF.encode Φ)) := by
  have h := Paper2.AEth5.twoCut_outputs K N₁ C.cR hN₁
    (EncodedCNF.encode Φ) tape
  simpa only [Paper2.AEth5.L1, hroute] using h

#print axioms twoCut_formula27

end Paper2.CurrentAdditive.QuarticClassEndpoint
