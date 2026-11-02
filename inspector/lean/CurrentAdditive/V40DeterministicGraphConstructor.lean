import CurrentAdditive.V40GraphConstructorRuntime
import CurrentAdditive.V40DeterministicRequest

namespace CurrentAdditive.V40DeterministicGraphConstructor
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction V38Schedule EncodedCommunication

def amplification := V40GraphConstructorRuntime.amplification
theorem amplification_ge (p : SourceConstants) : 2^64≤amplification p :=
  V40GraphConstructorRuntime.amplification_ge p
theorem amplification_power (p : SourceConstants) : ∃ a, amplification p=2^a :=
  V40GraphConstructorRuntime.amplification_power p

def matrix (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid) (floor K : Nat)
    (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :=
  publicGraphRunFrom p floor hn hlow hdegree (Paper2.CanonicalEdgeTape.graphEdge g hg) K

def context (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid) (floor : Nat)
    (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :=
  let L:=publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree
  let ht:=(publicLogFrom_spec p floor g.vertices g.edges.length hn hlow hdegree).2
  V40GraphConstructorWords.context g hg L (passing_s_ge_four _ _ _ _ _ ht) hn
    (passing_repetition_eq _ _ _ _ _ ht)

def envelopeWord (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid) (floor K : Nat)
    (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :=
  V40StoredEnvelope.input (publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree) K
    (context p g hg floor hn hlow hdegree) (matrix p g hg floor K hn hlow hdegree)

def squareWord (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid) (floor K : Nat)
    (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :=
  (matrix p g hg floor K hn hlow hdegree).squareWord

def rectangleWord (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid) (floor K : Nat)
    (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :=
  encodeInstance (V40StoredRectangle.rectangleInstance
    (publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree) K
    (matrix p g hg floor K hn hlow hdegree))

def requestWord (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid) (floor K : Nat)
    (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :=
  natField (2*publicGraphThresholdFrom p floor g.vertices g.edges.length hn hlow hdegree K+K)++
    squareWord p g hg floor K hn hlow hdegree

theorem word_eq (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid) (floor K : Nat)
    (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :
    let L:=publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree
    let ht:=(publicLogFrom_spec p floor g.vertices g.edges.length hn hlow hdegree).2
    V40GraphConstructorWords.word g hg L K (passing_s_ge_four _ _ _ _ _ ht) hn
      (passing_repetition_eq _ _ _ _ _ ht) K=envelopeWord p g hg floor K hn hlow hdegree := by
  unfold V40GraphConstructorWords.word envelopeWord context matrix
  dsimp only
  rw [V40GraphConstructorWords.run_public p g hg floor K hn hlow hdegree]

def envelopeMachine (p : SourceConstants) := V40GraphConstructorRuntime.machine p
  V40ConstructorRoundPacket.identity.machine
def squareMachine (p : SourceConstants) := V40GraphConstructorRuntime.machine p V40StoredEnvelope.machine
def rectangleMachine (p : SourceConstants) := V40GraphConstructorRuntime.machine p V40StoredEnvelope.rectangle.machine
def requestMachine (p : SourceConstants) := V40GraphConstructorRuntime.machine p V40DeterministicRequest.request.machine

def envelopeExponent (p : SourceConstants) := V40GraphConstructorRuntime.exponent p
  V40ConstructorRoundPacket.identity.machine 1 0
def squareExponent (p : SourceConstants) := V40GraphConstructorRuntime.exponent p
  V40StoredEnvelope.machine V40StoredEnvelope.coefficient V40StoredEnvelope.degree
def rectangleExponent (p : SourceConstants) := V40GraphConstructorRuntime.exponent p
  V40StoredEnvelope.rectangle.machine V40StoredEnvelope.rectangle.coefficient V40StoredEnvelope.rectangle.degree
def requestExponent (p : SourceConstants) := V40GraphConstructorRuntime.exponent p
  V40DeterministicRequest.request.machine V40DeterministicRequest.request.coefficient V40DeterministicRequest.request.degree

private theorem native_tail (p : SourceConstants) (T : BitMachine.Machine) (ct dt : Nat)
    (g : EncodedGraph.Graph) (hg : g.Valid) (floor K : Nat)
    (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) (Y : List Bool)
    (h : T.OutputsWithin (envelopeWord p g hg floor K hn hlow hdegree) Y
      (ct*((envelopeWord p g hg floor K hn hlow hdegree).length+1)^dt)) :
    let L:=publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree
    let ht:=(publicLogFrom_spec p floor g.vertices g.edges.length hn hlow hdegree).2
    let w:=V40GraphConstructorWords.word g hg L K
      (passing_s_ge_four _ _ _ _ _ ht) hn (passing_repetition_eq _ _ _ _ _ ht) K
    T.OutputsWithin w Y (ct*(w.length+1)^dt) := by
  dsimp only
  rw [word_eq p g hg floor K hn hlow hdegree]
  exact h

theorem envelope_outputs (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid)
    (floor K : Nat) (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :
    let N:=generatedN (publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree)
    (envelopeMachine p).OutputsWithin (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K)
      (envelopeWord p g hg floor K hn hlow hdegree) (N^(envelopeExponent p*(amplification p)^K)) := by
  apply V40GraphConstructorRuntime.outputs
  apply native_tail
  exact V40ConstructorRoundPacket.identity.outputs _

theorem square_outputs (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid)
    (floor K : Nat) (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :
    let N:=generatedN (publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree)
    (squareMachine p).OutputsWithin (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K)
      (squareWord p g hg floor K hn hlow hdegree) (N^(squareExponent p*(amplification p)^K)) := by
  apply V40GraphConstructorRuntime.outputs
  apply native_tail
  exact V40StoredEnvelope.outputs _ _ _ _

theorem rectangle_outputs (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid)
    (floor K : Nat) (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :
    let N:=generatedN (publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree)
    (rectangleMachine p).OutputsWithin (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K)
      (rectangleWord p g hg floor K hn hlow hdegree) (N^(rectangleExponent p*(amplification p)^K)) := by
  apply V40GraphConstructorRuntime.outputs
  apply native_tail
  exact V40StoredEnvelope.rectangle_outputs _ _ _ _

theorem request_outputs (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid)
    (floor K : Nat) (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :
    let N:=generatedN (publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree)
    (requestMachine p).OutputsWithin (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K)
      (requestWord p g hg floor K hn hlow hdegree) (N^(requestExponent p*(amplification p)^K)) := by
  apply V40GraphConstructorRuntime.outputs
  apply native_tail
  exact V40DeterministicRequest.public_outputs p floor hn hlow hdegree
    (Paper2.CanonicalEdgeTape.graphEdge g hg) K (context p g hg floor hn hlow hdegree)

def rectanglePolynomialDegree (p : SourceConstants) (K : Nat) :=
  V40GraphConstructorRuntime.baseExponent p V40StoredEnvelope.rectangle.machine
    V40StoredEnvelope.rectangle.coefficient V40StoredEnvelope.rectangle.degree*(amplification p)^K
def requestPolynomialDegree (p : SourceConstants) (K : Nat) :=
  V40GraphConstructorRuntime.baseExponent p V40DeterministicRequest.request.machine
    V40DeterministicRequest.request.coefficient V40DeterministicRequest.request.degree*(amplification p)^K

theorem rectangle_outputs_fixed_round (p : SourceConstants) (K : Nat)
    (g : EncodedGraph.Graph) (hg : g.Valid) (floor : Nat)
    (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :
    (rectangleMachine p).OutputsWithin (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K)
      (rectangleWord p g hg floor K hn hlow hdegree)
      (((V40GraphConstructorFront.input (EncodedGraph.encode g) floor K).length+1)^rectanglePolynomialDegree p K) := by
  apply V40GraphConstructorRuntime.outputs_fixed_round
  apply native_tail
  exact V40StoredEnvelope.rectangle_outputs _ _ _ _

theorem request_outputs_fixed_round (p : SourceConstants) (K : Nat)
    (g : EncodedGraph.Graph) (hg : g.Valid) (floor : Nat)
    (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :
    (requestMachine p).OutputsWithin (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K)
      (requestWord p g hg floor K hn hlow hdegree)
      (((V40GraphConstructorFront.input (EncodedGraph.encode g) floor K).length+1)^requestPolynomialDegree p K) := by
  apply V40GraphConstructorRuntime.outputs_fixed_round
  apply native_tail
  exact V40DeterministicRequest.public_outputs p floor hn hlow hdegree
    (Paper2.CanonicalEdgeTape.graphEdge g hg) K (context p g hg floor hn hlow hdegree)

theorem requestExponent_ge (p : SourceConstants) : 1040≤requestExponent p := by
  unfold requestExponent V40GraphConstructorRuntime.exponent
  omega

theorem envelope_length (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid)
    (floor K : Nat) (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :
    let N:=generatedN (publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree)
    (envelopeWord p g hg floor K hn hlow hdegree).length≤N^(envelopeExponent p*(amplification p)^K) := by
  apply V40GraphConstructorRuntime.output_length
  apply native_tail
  exact V40ConstructorRoundPacket.identity.outputs _

theorem square_length (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid)
    (floor K : Nat) (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :
    let N:=generatedN (publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree)
    (squareWord p g hg floor K hn hlow hdegree).length≤N^(squareExponent p*(amplification p)^K) := by
  apply V40GraphConstructorRuntime.output_length
  apply native_tail
  exact V40StoredEnvelope.outputs _ _ _ _

theorem rectangle_length (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid)
    (floor K : Nat) (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :
    let N:=generatedN (publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree)
    (rectangleWord p g hg floor K hn hlow hdegree).length≤N^(rectangleExponent p*(amplification p)^K) := by
  apply V40GraphConstructorRuntime.output_length
  apply native_tail
  exact V40StoredEnvelope.rectangle_outputs _ _ _ _

theorem request_length (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid)
    (floor K : Nat) (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :
    let N:=generatedN (publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree)
    (requestWord p g hg floor K hn hlow hdegree).length≤N^(requestExponent p*(amplification p)^K) := by
  apply V40GraphConstructorRuntime.output_length
  apply native_tail
  exact V40DeterministicRequest.public_outputs p floor hn hlow hdegree
    (Paper2.CanonicalEdgeTape.graphEdge g hg) K (context p g hg floor hn hlow hdegree)

#print axioms amplification_ge
#print axioms envelope_outputs
#print axioms square_outputs
#print axioms rectangle_outputs
#print axioms request_outputs
#print axioms rectangle_outputs_fixed_round
#print axioms request_outputs_fixed_round
#print axioms square_length
#print axioms rectangle_length
#print axioms request_length
end
end CurrentAdditive.V40DeterministicGraphConstructor
