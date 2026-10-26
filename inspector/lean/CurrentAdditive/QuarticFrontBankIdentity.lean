import CurrentAdditive.QuarticCutOutputCopies
import CurrentAdditive.QuarticSourceTapeFit

/-! Identify the physical raw cutter's exact packet with the v27 selected
bank on the scheduled branch. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open EthInapproximability.CurrentPaper

theorem cutPacket_eq_inputBank27
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin g.vertices) (Edges := Fin g.edges.length)
      (Nat.clog 2 g.vertices) Δ γ)
    (Φ : EncodedCNF.Formula) (fullTape : List Bool)
    (t : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape)
    (hfit : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).inputBits ≤
      Paper2.AEth3.cutLen Φ)
    (hbits : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t =
      fullTape.take
        (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).inputBits) :
    Paper2.CurrentAdditive.QuarticCutOutputCopies.outPacket g k
      ((fullTape.take (Paper2.AEth3.cutLen Φ)).take
        (QuarticCutCount.count27 g.vertices g.edges.length
          (Nat.clog 2 g.vertices) Δ γ k)) =
      QuarticDispatchSpec.inputBank27 Δ γ g hg hn k t := by
  have hcount := QuarticCutCount.count27_eq_select27_inputBits
    hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k hc
  have hraw : (fullTape.take (Paper2.AEth3.cutLen Φ)).take
      (QuarticCutCount.count27 g.vertices g.edges.length
        (Nat.clog 2 g.vertices) Δ γ k) =
      (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t := by
    rw [hcount, List.take_take, Nat.min_eq_left hfit]
    exact hbits.symm
  rw [hraw]
  rfl

#print axioms cutPacket_eq_inputBank27

end Paper2.CurrentAdditive.QuarticClassEndpoint
