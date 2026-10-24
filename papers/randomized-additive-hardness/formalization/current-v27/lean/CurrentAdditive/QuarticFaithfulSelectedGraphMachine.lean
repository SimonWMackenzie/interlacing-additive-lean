import CurrentAdditive.QuarticFaithfulSelected

/-! One-tape join: literal faithful selected bytes and the clocked recursive
graph-entry reader are about the same scheduled table. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384

namespace Paper2.GenericQuarticFaithful

open EthInapproximability.CurrentPaper
open Paper2.CurrentAdditive.QuarticConstructor

theorem selected_good_graph_machine (g : EncodedGraph.Graph) (hg : g.Valid)
    [NeZero g.vertices] (hn : 0 < g.vertices)
    (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin g.vertices) (Edges := Fin g.edges.length)
      (Nat.clog 2 g.vertices) Δ γ)
    (bits : (scheduledOutput27Faithful hn
      (CanonicalEdgeTape.graphEdge g hg) Δ γ k hc).Tape) :
    ((select27Faithful hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).table
      (selectedTape27Faithful hn (CanonicalEdgeTape.graphEdge g hg)
        Δ γ k hc bits)).bits =
      (table27Faithful hn (CanonicalEdgeTape.graphEdge g hg)
        (Nat.clog 2 g.vertices) Δ γ k hc bits).bits ∧
    (type_of% (graph_table_seed_machine g hg hn
      (Nat.clog 2 g.vertices) Δ γ k hc bits)) := by
  exact ⟨selected_good_table_bits hn (CanonicalEdgeTape.graphEdge g hg)
      Δ γ k hc bits,
    graph_table_seed_machine g hg hn (Nat.clog 2 g.vertices) Δ γ k hc bits⟩

#print axioms selected_good_graph_machine

end Paper2.GenericQuarticFaithful
