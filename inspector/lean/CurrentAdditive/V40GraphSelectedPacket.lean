import CurrentAdditive.V40GraphConstructorFront
import CurrentAdditive.V40ContextFirstPassingSearch

namespace CurrentAdditive.V40GraphSelectedPacket
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
open EthInapproximability.CurrentPaper V39GeneratedConstruction



def handCoefficient (p : SourceConstants) := Classical.choose (V40ContextFirstPassingSearch.outputs_polynomial p)
def handDegree (p : SourceConstants) := Classical.choose (Classical.choose_spec (V40ContextFirstPassingSearch.outputs_polynomial p))
theorem hand_outputs (p : SourceConstants) (context : List Bool) (floor n m : Nat)
    (hn : 0<n) (hlow : n≤2*m) (hdegree : 2*m≤p.degree*n) :
    (V40ContextFirstPassingSearch.machine p).OutputsWithin (V40ContextFirstPassingSearch.input context floor n m)
      (V40ContextFirstPassingSearch.output context (publicLogFrom p floor n m hn hlow hdegree))
      (handCoefficient p*((V40ContextFirstPassingSearch.input context floor n m).length+1)^handDegree p) :=
  Classical.choose_spec (Classical.choose_spec (V40ContextFirstPassingSearch.outputs_polynomial p))
    context floor n m hn hlow hdegree

def searchedMachine (p : SourceConstants) :=
  BitMachineComposition.composition V40GraphConstructorFront.searchPacket.machine (V40ContextFirstPassingSearch.machine p)
def searchedCoefficient (p : SourceConstants) := V40GraphConstructorFront.searchPacket.coefficient+
  2*(V40GraphConstructorFront.searchPacket.coefficient*V40GraphConstructorFront.searchPacket.machine.pushBound+1)+
  handCoefficient p*(V40GraphConstructorFront.searchPacket.coefficient*V40GraphConstructorFront.searchPacket.machine.pushBound+1)^handDegree p
def searchedDegree (p : SourceConstants) := (V40GraphConstructorFront.searchPacket.degree+1)*(handDegree p+1)

theorem searched_outputs (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid)
    (floor K : Nat) (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :
    let L := publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree
    (searchedMachine p).OutputsWithin (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K)
      (V40GraphConstructorFront.foundWord g floor K L)
      (searchedCoefficient p*((V40GraphConstructorFront.input (EncodedGraph.encode g) floor K).length+1)^searchedDegree p) := by
  let L := publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree
  have hf := V40GraphConstructorFront.search_outputs g hg floor K
  have hh := hand_outputs p (V40GraphConstructorFront.countWord g floor K) floor g.vertices g.edges.length hn hlow hdegree
  change (V40ContextFirstPassingSearch.machine p).OutputsWithin (V40GraphConstructorFront.searchWord g floor K) (V40GraphConstructorFront.foundWord g floor K L)
    (handCoefficient p*((V40GraphConstructorFront.searchWord g floor K).length+1)^handDegree p) at hh
  have h := BitMachineComposition.composition_outputsWithin V40GraphConstructorFront.searchPacket.machine (V40ContextFirstPassingSearch.machine p) hf hh
  apply BitMachine.outputsWithin_mono _ h
  exact BitMachineCompositionArithmetic.composition_time_bound
    (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K).length
    V40GraphConstructorFront.searchPacket.coefficient V40GraphConstructorFront.searchPacket.degree (handCoefficient p) (handDegree p)
    V40GraphConstructorFront.searchPacket.machine.pushBound (V40GraphConstructorFront.searchWord g floor K).length
    (BitMachine.output_length_bound V40GraphConstructorFront.searchPacket.machine hf)

def machine (p : SourceConstants) :=
  BitMachineComposition.composition (searchedMachine p) V40GraphConstructorFront.postSearch.machine
def coefficient (p : SourceConstants) := searchedCoefficient p+
  2*(searchedCoefficient p*(searchedMachine p).pushBound+1)+
  V40GraphConstructorFront.postSearch.coefficient*(searchedCoefficient p*(searchedMachine p).pushBound+1)^V40GraphConstructorFront.postSearch.degree
def degree (p : SourceConstants) := (searchedDegree p+1)*(V40GraphConstructorFront.postSearch.degree+1)

/-- Actual graph bytes and original variable floor feed the exact physical
first-passing search. No graph count or selected parameter is supplied. -/
theorem outputs (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid)
    (floor K : Nat) (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :
    let L := publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree
    (machine p).OutputsWithin (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K)
      (V40GraphConstructorFront.parameterWord g L K)
      (coefficient p*((V40GraphConstructorFront.input (EncodedGraph.encode g) floor K).length+1)^degree p) := by
  let L := publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree
  have hs := searched_outputs p g hg floor K hn hlow hdegree
  have hp := V40GraphConstructorFront.post_outputs g floor K L
  have h := BitMachineComposition.composition_outputsWithin (searchedMachine p)
    V40GraphConstructorFront.postSearch.machine hs hp
  apply BitMachine.outputsWithin_mono _ h
  exact BitMachineCompositionArithmetic.composition_time_bound
    (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K).length (searchedCoefficient p) (searchedDegree p)
    V40GraphConstructorFront.postSearch.coefficient V40GraphConstructorFront.postSearch.degree (searchedMachine p).pushBound
    (V40GraphConstructorFront.foundWord g floor K L).length
    (BitMachine.output_length_bound (searchedMachine p) hs)

#print axioms hand_outputs
#print axioms searched_outputs
#print axioms outputs
end
end CurrentAdditive.V40GraphSelectedPacket
