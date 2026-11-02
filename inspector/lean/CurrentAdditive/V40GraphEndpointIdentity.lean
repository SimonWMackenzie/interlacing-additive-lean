import CurrentAdditive.EdgeEncoder
import Paper2.CanonicalEdgeTape

namespace CurrentAdditive.V40GraphEndpointIdentity
open EthInapproximability.CurrentPaper

/-- Both adapters read the same ordered edge occurrence and the same
Boolean endpoint orientation. Proof fields of Fin do not alter the data. -/
theorem edge_eq (g : EncodedGraph.Graph) (hg : g.Valid) :
    LiteralEdgeEncoder.edge g hg=Paper2.CanonicalEdgeTape.graphEdge g hg := by
  funext e b
  apply Fin.ext
  cases b <;> simp [LiteralEdgeEncoder.edge,Paper2.CanonicalEdgeTape.graphEdge]

#print axioms edge_eq
end CurrentAdditive.V40GraphEndpointIdentity
