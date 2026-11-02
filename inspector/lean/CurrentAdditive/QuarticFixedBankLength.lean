import CurrentAdditive.QuarticFixedSquareClock

/-! The exact v27 input bank's serialized length depends on the formula and
selector dimensions, not on the fair tape values. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open EthInapproximability.CurrentPaper

def inputBankLength27 (Δ : ℕ) (γ : ℚ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (k : ℕ) : ℕ :=
  2 * ((EncodedGraph.encode g).length + k +
    (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).inputBits) + 3

theorem inputBank_encoded_length27
    (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph)
    (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ)
    (t : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) :
    (BitMachineBankCodec.encode
      (QuarticDispatchSpec.inputBank27 Δ γ g hg hn k t)).length =
      inputBankLength27 Δ γ g hg hn k := by
  rw [BitMachineBankCodec.encode_length]
  simp only [QuarticDispatchSpec.inputBank27, inputBankLength27,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, List.length_replicate]
  change 2 * ((EncodedGraph.encode g).length + k +
      ((select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t).length) + 3 =
    2 * ((EncodedGraph.encode g).length + k +
      (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).inputBits) + 3
  rw [QuarticInputSize.tapeBits_length27 hn
    (CanonicalEdgeTape.graphEdge g hg) Δ γ k t]

#print axioms inputBank_encoded_length27

end Paper2.CurrentAdditive.QuarticClassEndpoint
