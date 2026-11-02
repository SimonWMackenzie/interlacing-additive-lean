import CurrentAdditive.QuarticPrefixCarrier

/-! The exact reduction cut and a fitted classifier block fit the R20 tape. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.AEth4 Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper

theorem prefixReadFit27 (K N₁ : ℕ) (hN₁ : 1 ≤ N₁)
    (C : Paper2.SelectedTape.Algorithm)
    (x : List Bool) (Φ : EncodedCNF.Formula)
    (hroute : routed4 K N₁ x = Φ)
    (w : List Bool)
    (hfit : C.tapeLength w ≤ C.cR * Paper2.AEth.expLen Φ.variables) :
    Paper2.AEth3.cutLen Φ + C.tapeLength w ≤
      tapeCA (phiLen N₁) (8 + C.cR) x.length := by
  have hblocks := blocks_fit K hN₁ C.cR x
  rw [hroute] at hblocks
  omega

#print axioms prefixReadFit27

end Paper2.CurrentAdditive.QuarticClassEndpoint
