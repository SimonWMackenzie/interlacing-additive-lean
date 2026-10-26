import CurrentAdditive.QuarticPhysicalOutput

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open EthInapproximability.CurrentPaper
open Paper2 Paper2.AEth4

set_option maxHeartbeats 2000000

theorem headerClock27_le (Φ : EncodedCNF.Formula)
    (bank : List Bool) (i : EncodedCommunication.Instance)
    (T₀ Z : ℕ)
    (he : (EncodedCNF.encode Φ).length ≤ Z)
    (hb : bank.length ≤ Z)
    (hs : (EncodedCommunication.encodeInstance
      (Paper2.ASquare.squareInstance i)).length ≤ Z)
    (ht : T₀ ≤ Z)
    (hk : KHeader.clock Φ (Paper2.ASquare.squareInstance i) ≤ Z) :
    headerClock27 Φ bank i T₀ ≤ 200 * (Z + 1) := by
  unfold headerClock27
  simp only [EncodedComplexity.pair_length,
    EncodedCommunication.field_length, List.length_nil]
  omega

#print axioms headerClock27_le

end Paper2.CurrentAdditive.QuarticClassEndpoint
