import CurrentAdditive.V40DeterministicGraphConstructor

namespace CurrentAdditive.V40DeterministicGraphConstructor
noncomputable section
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction V38Schedule

/-- An admissible supplied dyadic order is retained exactly. This uses
the literal passing tests, rather than a sufficient large-order cutoff. -/
theorem rectangle_outputs_dyadic (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid)
    (L K : Nat) (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) (hnN : g.vertices≤2^L)
    (ht : GeneratedTests p.deletion L g.edges.length
      (sourceDeltaV p.gamma p.degree g.vertices g.edges.length) (sourceZeta p.gamma)) :
    (rectangleMachine p).OutputsWithin (V40GraphConstructorFront.input (EncodedGraph.encode g) (2^L) K)
      (rectangleWord p g hg (2^L) K hn hlow hdegree)
      ((2^L)^(rectangleExponent p*(amplification p)^K)) := by
  have hL:=V40GraphConstructorWords.publicLogFrom_eq_dyadic p _ _ L hn hlow hdegree hnN ht
  simpa only [hL,generatedN] using rectangle_outputs p g hg (2^L) K hn hlow hdegree

theorem square_outputs_dyadic (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid)
    (L K : Nat) (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) (hnN : g.vertices≤2^L)
    (ht : GeneratedTests p.deletion L g.edges.length
      (sourceDeltaV p.gamma p.degree g.vertices g.edges.length) (sourceZeta p.gamma)) :
    (squareMachine p).OutputsWithin (V40GraphConstructorFront.input (EncodedGraph.encode g) (2^L) K)
      (squareWord p g hg (2^L) K hn hlow hdegree)
      ((2^L)^(squareExponent p*(amplification p)^K)) := by
  have hL:=V40GraphConstructorWords.publicLogFrom_eq_dyadic p _ _ L hn hlow hdegree hnN ht
  simpa only [hL,generatedN] using square_outputs p g hg (2^L) K hn hlow hdegree

theorem request_outputs_dyadic (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid)
    (L K : Nat) (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) (hnN : g.vertices≤2^L)
    (ht : GeneratedTests p.deletion L g.edges.length
      (sourceDeltaV p.gamma p.degree g.vertices g.edges.length) (sourceZeta p.gamma)) :
    (requestMachine p).OutputsWithin (V40GraphConstructorFront.input (EncodedGraph.encode g) (2^L) K)
      (requestWord p g hg (2^L) K hn hlow hdegree)
      ((2^L)^(requestExponent p*(amplification p)^K)) := by
  have hL:=V40GraphConstructorWords.publicLogFrom_eq_dyadic p _ _ L hn hlow hdegree hnN ht
  simpa only [hL,generatedN] using request_outputs p g hg (2^L) K hn hlow hdegree

theorem rectangle_length_dyadic (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid)
    (L K : Nat) (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) (hnN : g.vertices≤2^L)
    (ht : GeneratedTests p.deletion L g.edges.length
      (sourceDeltaV p.gamma p.degree g.vertices g.edges.length) (sourceZeta p.gamma)) :
    (rectangleWord p g hg (2^L) K hn hlow hdegree).length≤
      (2^L)^(rectangleExponent p*(amplification p)^K) := by
  have hL:=V40GraphConstructorWords.publicLogFrom_eq_dyadic p _ _ L hn hlow hdegree hnN ht
  simpa only [hL,generatedN] using rectangle_length p g hg (2^L) K hn hlow hdegree

theorem square_length_dyadic (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid)
    (L K : Nat) (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) (hnN : g.vertices≤2^L)
    (ht : GeneratedTests p.deletion L g.edges.length
      (sourceDeltaV p.gamma p.degree g.vertices g.edges.length) (sourceZeta p.gamma)) :
    (squareWord p g hg (2^L) K hn hlow hdegree).length≤
      (2^L)^(squareExponent p*(amplification p)^K) := by
  have hL:=V40GraphConstructorWords.publicLogFrom_eq_dyadic p _ _ L hn hlow hdegree hnN ht
  simpa only [hL,generatedN] using square_length p g hg (2^L) K hn hlow hdegree

theorem request_length_dyadic (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid)
    (L K : Nat) (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) (hnN : g.vertices≤2^L)
    (ht : GeneratedTests p.deletion L g.edges.length
      (sourceDeltaV p.gamma p.degree g.vertices g.edges.length) (sourceZeta p.gamma)) :
    (requestWord p g hg (2^L) K hn hlow hdegree).length≤
      (2^L)^(requestExponent p*(amplification p)^K) := by
  have hL:=V40GraphConstructorWords.publicLogFrom_eq_dyadic p _ _ L hn hlow hdegree hnN ht
  simpa only [hL,generatedN] using request_length p g hg (2^L) K hn hlow hdegree

#print axioms rectangle_outputs_dyadic
#print axioms square_outputs_dyadic
#print axioms request_outputs_dyadic
#print axioms rectangle_length_dyadic
#print axioms square_length_dyadic
#print axioms request_length_dyadic
end
end CurrentAdditive.V40DeterministicGraphConstructor
