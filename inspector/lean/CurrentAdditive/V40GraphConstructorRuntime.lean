import CurrentAdditive.V40GraphSeedPrefix
import CurrentAdditive.V40GraphRoundInstance
import CurrentAdditive.V40GraphConstructorInputBounds
import CurrentAdditive.V40PipelineRuntime

namespace CurrentAdditive.V40GraphConstructorRuntime
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction V38Schedule

def amplification (p : SourceConstants) := V40PipelineRuntime.amplification
  (V40GraphSeedPrefix.machine p) StoredMatrixEnvelopeStep.machine 2 1
  (V40GraphSeedPrefix.baseCoefficient p) (V40GraphSeedPrefix.degree p)
  StoredMatrixEnvelopeStep.coefficient StoredMatrixEnvelopeStep.degree

def baseExponent (p : SourceConstants) (T : BitMachine.Machine) (ct dt : Nat) :=
  V40PipelineRuntime.exponentCoefficient
    (V40GraphSeedPrefix.machine p) StoredMatrixEnvelopeStep.machine T 2 1
    (V40GraphSeedPrefix.baseCoefficient p) (V40GraphSeedPrefix.degree p)
    StoredMatrixEnvelopeStep.coefficient StoredMatrixEnvelopeStep.degree ct dt

def exponent (p : SourceConstants) (T : BitMachine.Machine) (ct dt : Nat) :=
  (V40GraphConstructorInputBounds.dyadicBaseCoefficient p+2)*baseExponent p T ct dt+1040

def machine (p : SourceConstants) (T : BitMachine.Machine) := V40PipelineRuntime.pipeline
  (V40GraphSeedPrefix.machine p) StoredMatrixEnvelopeStep.machine T

theorem amplification_ge (p : SourceConstants) : 2^64≤amplification p :=
  V40PipelineRuntime.amplification_ge _ _ _ _ _ _ _ _

theorem amplification_power (p : SourceConstants) : ∃ a, amplification p=2^a :=
  ⟨V40PipelineRuntime.amplificationLog _ _ 2 1
    (V40GraphSeedPrefix.baseCoefficient p) (V40GraphSeedPrefix.degree p)
    StoredMatrixEnvelopeStep.coefficient StoredMatrixEnvelopeStep.degree,rfl⟩

/-- The prefix and every update are the concrete checked machines. This
helper permits a separately checked physical tail; the public endpoints below
instantiate it with the actual formatters. -/
theorem outputs_base_with_length (p : SourceConstants) (T : BitMachine.Machine) (ct dt : Nat)
    (g : EncodedGraph.Graph) (hg : g.Valid) (floor K : Nat)
    (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) (Y : List Bool)
    (hT : let L:=publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree
      let ht:=(publicLogFrom_spec p floor g.vertices g.edges.length hn hlow hdegree).2
      let w:=V40GraphConstructorWords.word g hg L K
        (passing_s_ge_four _ _ _ _ _ ht) hn (passing_repetition_eq _ _ _ _ _ ht) K
      T.OutputsWithin w Y (ct*(w.length+1)^dt)) :
    (machine p T).OutputsWithin (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K) Y
      ((V40GraphConstructorInputBounds.base g floor)^(baseExponent p T ct dt*(amplification p)^K)) ∧
    Y.length≤(V40GraphConstructorInputBounds.base g floor)^(baseExponent p T ct dt*(amplification p)^K) := by
  let L:=publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree
  have ht:=(publicLogFrom_spec p floor g.vertices g.edges.length hn hlow hdegree).2
  have hs : 4≤generatedS L:=passing_s_ge_four _ _ _ _ _ ht
  have hq : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) g.edges.length
      (publicRepetition L g.edges.length):=passing_repetition_eq _ _ _ _ _ ht
  let words:=V40GraphConstructorWords.word g hg L K hs hn hq
  have hx : (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K).length≤
      2*(V40GraphConstructorInputBounds.base g floor+K+1)^1 := by
    rw [pow_one]
    have h:=V40GraphConstructorInputBounds.input_length g floor K
    omega
  exact (V40PipelineRuntime.outputs (V40GraphSeedPrefix.machine p) StoredMatrixEnvelopeStep.machine T
    2 1 (V40GraphSeedPrefix.baseCoefficient p) (V40GraphSeedPrefix.degree p)
    StoredMatrixEnvelopeStep.coefficient StoredMatrixEnvelopeStep.degree ct dt
    (V40GraphConstructorInputBounds.base g floor) K
    (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K) words Y
    (V40GraphConstructorInputBounds.base_ge_two g floor) hx
    (V40GraphSeedPrefix.outputs_base p g hg floor K hn hlow hdegree)
    (V40GraphRoundInstance.outputs g hg L K hs hn hq) hT)

theorem outputs_base (p : SourceConstants) (T : BitMachine.Machine) (ct dt : Nat)
    (g : EncodedGraph.Graph) (hg : g.Valid) (floor K : Nat)
    (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) (Y : List Bool)
    (hT : let L:=publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree
      let ht:=(publicLogFrom_spec p floor g.vertices g.edges.length hn hlow hdegree).2
      let w:=V40GraphConstructorWords.word g hg L K
        (passing_s_ge_four _ _ _ _ _ ht) hn (passing_repetition_eq _ _ _ _ _ ht) K
      T.OutputsWithin w Y (ct*(w.length+1)^dt)) :
    (machine p T).OutputsWithin (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K) Y
      ((V40GraphConstructorInputBounds.base g floor)^(baseExponent p T ct dt*(amplification p)^K)) :=
  (outputs_base_with_length p T ct dt g hg floor K hn hlow hdegree Y hT).1

/-- The base is the selected dyadic size of the actual first-passing
construction. It excludes the round count. The amplification was fixed
before the tail and its clock constants. -/
theorem outputs (p : SourceConstants) (T : BitMachine.Machine) (ct dt : Nat)
    (g : EncodedGraph.Graph) (hg : g.Valid) (floor K : Nat)
    (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) (Y : List Bool)
    (hT : let L:=publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree
      let ht:=(publicLogFrom_spec p floor g.vertices g.edges.length hn hlow hdegree).2
      let w:=V40GraphConstructorWords.word g hg L K
        (passing_s_ge_four _ _ _ _ _ ht) hn (passing_repetition_eq _ _ _ _ _ ht) K
      T.OutputsWithin w Y (ct*(w.length+1)^dt)) :
    let N:=generatedN (publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree)
    (machine p T).OutputsWithin (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K) Y
      (N^(exponent p T ct dt*(amplification p)^K)) := by
  have h:=outputs_base p T ct dt g hg floor K hn hlow hdegree Y hT
  apply BitMachine.outputsWithin_mono _ h
  exact V40GraphConstructorInputBounds.dyadic_clock_bound _ _ _ _ _ _ _
    (V40GraphConstructorInputBounds.generated_base_ge_two p floor _ _ hn hlow hdegree)
    (V40GraphConstructorInputBounds.base_le_dyadic p g hg floor hn hlow hdegree) le_rfl

theorem output_length (p : SourceConstants) (T : BitMachine.Machine) (ct dt : Nat)
    (g : EncodedGraph.Graph) (hg : g.Valid) (floor K : Nat)
    (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) (Y : List Bool)
    (hT : let L:=publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree
      let ht:=(publicLogFrom_spec p floor g.vertices g.edges.length hn hlow hdegree).2
      let w:=V40GraphConstructorWords.word g hg L K
        (passing_s_ge_four _ _ _ _ _ ht) hn (passing_repetition_eq _ _ _ _ _ ht) K
      T.OutputsWithin w Y (ct*(w.length+1)^dt)) :
    let N:=generatedN (publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree)
    Y.length≤N^(exponent p T ct dt*(amplification p)^K) := by
  exact V40GraphConstructorInputBounds.dyadic_clock_bound _ _ _ _ _ _ _
    (V40GraphConstructorInputBounds.generated_base_ge_two p floor _ _ hn hlow hdegree)
    (V40GraphConstructorInputBounds.base_le_dyadic p g hg floor hn hlow hdegree)
    (outputs_base_with_length p T ct dt g hg floor K hn hlow hdegree Y hT).2

/-- For each fixed round count this same physical program has a fixed
polynomial bound in its complete canonical graph/floor/round input. -/
theorem outputs_fixed_round (p : SourceConstants) (T : BitMachine.Machine) (ct dt K : Nat)
    (g : EncodedGraph.Graph) (hg : g.Valid) (floor : Nat)
    (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) (Y : List Bool)
    (hT : let L:=publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree
      let ht:=(publicLogFrom_spec p floor g.vertices g.edges.length hn hlow hdegree).2
      let w:=V40GraphConstructorWords.word g hg L K
        (passing_s_ge_four _ _ _ _ _ ht) hn (passing_repetition_eq _ _ _ _ _ ht) K
      T.OutputsWithin w Y (ct*(w.length+1)^dt)) :
    (machine p T).OutputsWithin (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K) Y
      (((V40GraphConstructorFront.input (EncodedGraph.encode g) floor K).length+1)^
        (baseExponent p T ct dt*(amplification p)^K)) := by
  apply BitMachine.outputsWithin_mono _ (outputs_base p T ct dt g hg floor K hn hlow hdegree Y hT)
  exact Nat.pow_le_pow_left (V40GraphConstructorInputBounds.base_le_input g floor K) _

#print axioms amplification_ge
#print axioms outputs
#print axioms output_length
#print axioms outputs_fixed_round
end
end CurrentAdditive.V40GraphConstructorRuntime
