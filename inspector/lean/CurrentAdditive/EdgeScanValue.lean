import CurrentAdditive.EdgeScanJoin
import CurrentAdditive.EdgeActivityRank
import CurrentAdditive.EdgeMatrixProductionConjugacy

namespace CurrentAdditive.LiteralEdgeScanValue

open Paper2
open EthInapproximability.CurrentPaper
open LiteralEdgeEncoder

theorem edge_eq_canonical (g : EncodedGraph.Graph) (hg : g.Valid) :
    edge g hg = CanonicalEdgeTape.graphEdge g hg := by
  funext e b
  apply Fin.ext
  cases b <;> simp [edge,CanonicalEdgeTape.graphEdge_false,CanonicalEdgeTape.graphEdge_true]

theorem scan_value_none {s r : ℕ} [NeZero s]
    (g : EncodedGraph.Graph) (hg : g.Valid) (hs : 3 ≤ s)
    (ig : Fin (4*s)) (z : Fin g.vertices ⊕ Fin (s-3))
    (a : Fin (Width s g.edges.length r))
    (ha : ¬ (0 < g.edges.length ∧ a.val / r / g.edges.length = ig.val)) :
    activity hs (edge g hg) (ig,z) a = none :=
  activity_none hs _ ig z a ha

/-- The actual physical output cells equal the current executable activity,
including the ordered active rank, on every selected public selector. -/
theorem scan_value_some {s r : ℕ} [NeZero s]
    (g : EncodedGraph.Graph) (hg : g.Valid) (hs : 3 ≤ s)
    (ig : Fin (4*s)) (z : Fin g.vertices ⊕ Fin (s-3))
    (a : Fin (Width s g.edges.length r))
    (ha : 0 < g.edges.length ∧ a.val / r / g.edges.length = ig.val) :
    let j : Fin g.edges.length := ⟨a.val / r % g.edges.length, Nat.mod_lt _ ha.1⟩
    let W := LiteralEdgeScanJoin.Wtrue g hg a.val r ig.val
      (CanonicalEndpointRankBridge.itemValue z) z.isRight j
    ∃ act rank, W LiteralEdgeScanJoin.actC = [act] ∧
      W (.inr (.inr 3)) = List.replicate rank true ∧
      Option.map Fin.val (activity hs (edge g hg) (ig,z) a) =
        if act then some rank else none := by
  intro j W
  refine ⟨CanonicalEndpointRankMachine.semanticActive (RankRun.kindOfNat 0)
      (RankRun.itemOfBool z.isRight)
      (CanonicalEdgeTape.graphEdge g hg j false).val
      (CanonicalEdgeTape.graphEdge g hg j true).val (CanonicalEndpointRankBridge.itemValue z),
    CanonicalEndpointRankMachine.semanticRank (RankRun.kindOfNat 0)
      (RankRun.itemOfBool z.isRight)
      (CanonicalEdgeTape.graphEdge g hg j false).val
      (CanonicalEdgeTape.graphEdge g hg j true).val (CanonicalEndpointRankBridge.itemValue z),
    LiteralEdgeScanJoin.Wtrue_act _ _ _ _ _ _ _ _,
    LiteralEdgeScanJoin.Wtrue_rank _ _ _ _ _ _ _ _, ?_⟩
  rw [activity_selected hs (edge g hg) ig z a ha,edge_eq_canonical]
  simp only [RankRun.kindOfNat,ite_true,RankRun.itemOfBool_isRight]
  rfl

#print axioms edge_eq_canonical
#print axioms scan_value_none
#print axioms scan_value_some

end CurrentAdditive.LiteralEdgeScanValue
