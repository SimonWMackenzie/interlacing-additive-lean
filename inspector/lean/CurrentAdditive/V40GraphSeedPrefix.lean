import CurrentAdditive.V40GraphSourcePrefix
import CurrentAdditive.V40ConstructorSeedAssembly

namespace CurrentAdditive.V40GraphSeedPrefix
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction V38Schedule

def machine (p : SourceConstants) := BitMachineComposition.composition
  (V40GraphSourcePrefix.machine p) V40ConstructorSeedAssembly.roundMachine
def coefficient (p : SourceConstants) := V40ConstructorComposition.coefficient
  (V40GraphSourcePrefix.coefficient p) (V40GraphSourcePrefix.degree p)
  V40ConstructorSeedAssembly.roundCoefficient V40ConstructorSeedAssembly.roundDegree
  (V40GraphSourcePrefix.machine p).pushBound (V40GraphParameterPrefix.dyadicCoefficient p)
def degree (p : SourceConstants) := V40ConstructorComposition.degree
  (V40GraphSourcePrefix.degree p) V40ConstructorSeedAssembly.roundDegree

/-- This is the actual graph-to-initial-iteration packet. The source law,
activity, context, seed and unary fuel are all physically produced. -/
theorem outputs (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid)
    (floor K : Nat) (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :
    let L := publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree
    let ht := (publicLogFrom_spec p floor g.vertices g.edges.length hn hlow hdegree).2
    (machine p).OutputsWithin (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K)
      (WeightedIterationDriver.input (V40GraphConstructorWords.word g hg L K
        (passing_s_ge_four _ _ _ _ _ ht) hn (passing_repetition_eq _ _ _ _ _ ht) 0) K)
      (coefficient p*((V40GraphConstructorFront.input (EncodedGraph.encode g) floor K).length+1)^degree p) := by
  let L := publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree
  have ht := (publicLogFrom_spec p floor g.vertices g.edges.length hn hlow hdegree).2
  have hs : 4≤generatedS L := passing_s_ge_four _ _ _ _ _ ht
  have hq : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) g.edges.length
      (publicRepetition L g.edges.length) := passing_repetition_eq _ _ _ _ _ ht
  have hp := V40GraphSourcePrefix.outputs p g hg floor K hn hlow hdegree
  have hw := V40ConstructorSeedAssembly.round_outputs (EncodedGraph.encode g) g.vertices g.edges.length L K
    (StoredWeightedState.lawBytes (V40GraphConstructorWords.law g L hs hn))
    (StoredStepContext.activityWords (V40GraphConstructorWords.activity g hg L hs hq))
    (V40ActualPreparedSearch.selected_ge_two p floor g.vertices g.edges.length hn hlow hdegree)
  change V40ConstructorSeedAssembly.roundMachine.OutputsWithin
    (V40GraphConstructorWords.source g hg L K hs hn hq)
    (WeightedIterationDriver.input (V40GraphConstructorWords.word g hg L K hs hn hq 0) K)
    (V40ConstructorSeedAssembly.roundCoefficient*
      (2^L+(V40GraphConstructorWords.source g hg L K hs hn hq).length+1)^V40ConstructorSeedAssembly.roundDegree) at hw
  have h := BitMachineComposition.composition_outputsWithin (V40GraphSourcePrefix.machine p)
    V40ConstructorSeedAssembly.roundMachine hp hw
  apply BitMachine.outputsWithin_mono _ h
  exact V40ConstructorComposition.time_bound
    (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K).length
    (V40GraphSourcePrefix.coefficient p) (V40GraphSourcePrefix.degree p)
    V40ConstructorSeedAssembly.roundCoefficient V40ConstructorSeedAssembly.roundDegree
    (V40GraphSourcePrefix.machine p).pushBound (V40GraphParameterPrefix.dyadicCoefficient p) (2^L)
    (V40GraphConstructorWords.source g hg L K hs hn hq).length
    (V40GraphParameterPrefix.dyadic_bound p g floor K hn hlow hdegree)
    (BitMachine.output_length_bound (V40GraphSourcePrefix.machine p) hp)

def baseCoefficient (p : SourceConstants) := coefficient p*2^degree p

theorem outputs_base (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid)
    (floor K : Nat) (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :
    let L := publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree
    let ht := (publicLogFrom_spec p floor g.vertices g.edges.length hn hlow hdegree).2
    (machine p).OutputsWithin (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K)
      (WeightedIterationDriver.input (V40GraphConstructorWords.word g hg L K
        (passing_s_ge_four _ _ _ _ _ ht) hn (passing_repetition_eq _ _ _ _ _ ht) 0) K)
      (baseCoefficient p*((EncodedGraph.encode g).length+floor+2+K+1)^degree p) := by
  apply BitMachine.outputsWithin_mono _ (outputs p g hg floor K hn hlow hdegree)
  rw [V40GraphParameterPrefix.input_length]
  calc
    _ ≤ coefficient p*(2*((EncodedGraph.encode g).length+floor+2+K+1))^degree p := by
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = _ := by rw [mul_pow];unfold baseCoefficient;ring

#print axioms outputs
#print axioms outputs_base
end
end CurrentAdditive.V40GraphSeedPrefix
