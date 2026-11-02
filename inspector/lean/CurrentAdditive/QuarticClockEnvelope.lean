import CurrentAdditive.QuarticClassifierClockBound

/-! A uniform polynomial envelope for the fixed v27 decision composition. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open EthInapproximability.CurrentPaper
open Paper2
open Paper2.AEth4

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem sourceDecisionClock27_le
    (C : Paper2.SelectedTape.Algorithm)
    (Φ : EncodedCNF.Formula)
    (raw block bank w : List Bool)
    (i : EncodedCommunication.Instance)
    (Ttwo Tcut Tprint Y Z : ℕ)
    (he : (EncodedCNF.encode Φ).length ≤ Z)
    (hf : (Paper2.AEth3.fOut Φ).length ≤ Z)
    (hr : raw.length ≤ Z)
    (hblock : block.length ≤ Z)
    (hbank : bank.length ≤ Z)
    (hs : (EncodedCommunication.encodeInstance
      (Paper2.ASquare.squareInstance i)).length ≤ Z)
    (hw : w.length ≤ Z)
    (htwo : Ttwo ≤ Z)
    (hcut : Tcut ≤ Z)
    (hprint : Tprint ≤ Z)
    (hy : Y ≤ Z)
    (hk : KHeader.clock Φ (Paper2.ASquare.squareInstance i) ≤ Z) :
    let Ttail := Tcut + 2 * (EncodedComplexity.pair
      (EncodedCNF.encode Φ) bank).length + 2 +
      headerClock27 Φ bank i
        ((EncodedCNF.encode Φ).length + 2 + 2 * bank.length + 2 + Tprint)
    sourceDecisionClock27 C (EncodedCNF.encode Φ) (Paper2.AEth3.fOut Φ)
      raw block w Ttwo (sourceCoreClock27 Φ raw Ttail) Y ≤
      5000 * (Z + 1) + Paper2.AEth5.clsTime C Z Z := by
  intro Ttail
  have ht0 : (EncodedCNF.encode Φ).length + 2 + 2 * bank.length + 2 + Tprint ≤
      7 * (Z + 1) := by omega
  have hkh := headerClock27_le Φ bank i _ (7 * (Z + 1))
    (by omega) (by omega) (by omega) ht0 (by omega)
  have hcls := clsTime_mono27 C hw hy
  have hpair : (EncodedComplexity.pair (EncodedCNF.encode Φ) bank).length ≤
      3 * (Z + 1) := by
    rw [EncodedComplexity.pair_length]
    omega
  dsimp only [Ttail]
  unfold sourceDecisionClock27 sourceCoreClock27
  simp only [EncodedComplexity.pair_length] at *
  omega

#print axioms sourceDecisionClock27_le

end Paper2.CurrentAdditive.QuarticClassEndpoint
