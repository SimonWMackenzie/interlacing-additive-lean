import CurrentAdditive.V40GraphConstructorWords
import CurrentAdditive.StoredMatrixEnvelopeStep

namespace CurrentAdditive.V40GraphRoundInstance
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction V38Schedule

/-- The step's actual data contain the literal public scalars and the current
stored matrix. No future table, source array or running time is supplied. -/
def data (g : EncodedGraph.Graph) (hg : g.Valid) (L : Nat) (hs : 4≤generatedS L)
    (hn : 0<g.vertices)
    (hq : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) g.edges.length
      (publicRepetition L g.edges.length)) (R : StoredMatrix) : StoredRoundData.Data where
  parameters := {
    q₁ := generatedQ₁ L
    q₂ := generatedQ₂ L
    s := generatedS L
    w := generatedW L
    Q := generatedQ L
    ni := 4*generatedS L*(g.vertices+(generatedS L-3))
    hq₁ := by unfold generatedQ₁;omega
    hq₂ := by unfold generatedQ₂ generatedN;positivity
    hs := by omega
    hw := by unfold generatedW generatedN;positivity
    hQ := by unfold generatedQ generatedN;positivity
    μI := V40GraphConstructorWords.law g L hs hn
    R := R }
  activity := V40GraphConstructorWords.activity g hg L hs hq

/-- The concrete one-round program applies at every natural round index,
with the same fixed coefficient and exponent before all graphs and states. -/
theorem outputs (g : EncodedGraph.Graph) (hg : g.Valid) (L K : Nat)
    (hs : 4≤generatedS L) (hn : 0<g.vertices)
    (hq : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) g.edges.length
      (publicRepetition L g.edges.length)) (j : Nat) :
    StoredMatrixEnvelopeStep.machine.OutputsWithin
      (V40GraphConstructorWords.word g hg L K hs hn hq j)
      (V40GraphConstructorWords.word g hg L K hs hn hq (j+1))
      (StoredMatrixEnvelopeStep.coefficient*
        ((V40GraphConstructorWords.word g hg L K hs hn hq j).length+1)^StoredMatrixEnvelopeStep.degree) := by
  have h := StoredMatrixEnvelopeStep.outputs
    (data g hg L hs hn hq (V40GraphConstructorWords.run g hg L hs hn hq j)) L K
  exact h

#print axioms outputs
end
end CurrentAdditive.V40GraphRoundInstance
