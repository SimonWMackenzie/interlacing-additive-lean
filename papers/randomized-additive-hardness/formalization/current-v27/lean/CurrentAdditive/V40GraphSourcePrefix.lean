import CurrentAdditive.V40GraphParameterPrefix
import CurrentAdditive.V40GraphConstructorWords
import CurrentAdditive.V40SourceContextWriter

namespace CurrentAdditive.V40GraphSourcePrefix
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction V38Schedule

def machine (p : SourceConstants) := BitMachineComposition.composition
  (V40GraphParameterPrefix.machine p) V40SourceContextWriter.machine
def coefficient (p : SourceConstants) := V40GraphParameterPrefix.coefficient p+
  2*(V40GraphParameterPrefix.coefficient p*(V40GraphParameterPrefix.machine p).pushBound+1)+
  V40SourceContextWriter.coefficient*
    (V40GraphParameterPrefix.coefficient p*(V40GraphParameterPrefix.machine p).pushBound+1)^V40SourceContextWriter.degree
def degree (p : SourceConstants) := (V40GraphParameterPrefix.degree p+1)*(V40SourceContextWriter.degree+1)

/-- The graph, original floor and rounds physically produce every scalar,
the exact canonical item law and the entire ordered activity table. -/
theorem outputs (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid)
    (floor K : Nat) (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :
    let L := publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree
    let ht := (publicLogFrom_spec p floor g.vertices g.edges.length hn hlow hdegree).2
    (machine p).OutputsWithin (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K)
      (V40GraphConstructorWords.source g hg L K
        (passing_s_ge_four _ _ _ _ _ ht) hn (passing_repetition_eq _ _ _ _ _ ht))
      (coefficient p*((V40GraphConstructorFront.input (EncodedGraph.encode g) floor K).length+1)^degree p) := by
  let L := publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree
  have ht := (publicLogFrom_spec p floor g.vertices g.edges.length hn hlow hdegree).2
  have hs : 4≤generatedS L := passing_s_ge_four _ _ _ _ _ ht
  have hq : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) g.edges.length
      (publicRepetition L g.edges.length) := passing_repetition_eq _ _ _ _ _ ht
  haveI : NeZero (generatedS L) := ⟨by change generatedS L≠0;omega⟩
  have hp := V40GraphParameterPrefix.outputs p g hg floor K hn hlow hdegree
  have hw := V40SourceContextWriter.outputs g hg L K hn hs hq
  change V40SourceContextWriter.machine.OutputsWithin
    (D22PostSearchPacket.output (EncodedGraph.encode g) g.vertices g.edges.length L K)
    (V40GraphConstructorWords.source g hg L K hs hn hq)
    (V40SourceContextWriter.coefficient*
      ((D22PostSearchPacket.output (EncodedGraph.encode g) g.vertices g.edges.length L K).length+1)^V40SourceContextWriter.degree) at hw
  have h := BitMachineComposition.composition_outputsWithin (V40GraphParameterPrefix.machine p)
    V40SourceContextWriter.machine hp hw
  apply BitMachine.outputsWithin_mono _ h
  exact BitMachineCompositionArithmetic.composition_time_bound
    (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K).length
    (V40GraphParameterPrefix.coefficient p) (V40GraphParameterPrefix.degree p)
    V40SourceContextWriter.coefficient V40SourceContextWriter.degree
    (V40GraphParameterPrefix.machine p).pushBound
    (D22PostSearchPacket.output (EncodedGraph.encode g) g.vertices g.edges.length L K).length
    (BitMachine.output_length_bound (V40GraphParameterPrefix.machine p) hp)

#print axioms outputs
end
end CurrentAdditive.V40GraphSourcePrefix
