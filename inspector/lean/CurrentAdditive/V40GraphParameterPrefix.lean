import CurrentAdditive.V40GraphSelectedPacket
import CurrentAdditive.V40ConstructorComposition
import CurrentAdditive.D22PostSearchCompiler

namespace CurrentAdditive.V40GraphParameterPrefix
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction V38Schedule

def dyadicCoefficient (p : SourceConstants) :=
  2*(generatedN (GeneratedCutoff.cutoffLog p.degree p.deletion)+1)

theorem input_length (graph : List Bool) (floor K : Nat) :
    (V40GraphConstructorFront.input graph floor K).length+1=2*(graph.length+floor+K+2) := by
  simp [V40GraphConstructorFront.input,BitMachineBankCodec.encode_length,Fin.sum_univ_succ]
  ring

theorem dyadic_bound (p : SourceConstants) (g : EncodedGraph.Graph) (floor K : Nat)
    (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :
    2^(publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree) ≤
      dyadicCoefficient p*((V40GraphConstructorFront.input (EncodedGraph.encode g) floor K).length+1) := by
  let Z := (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K).length+1
  let B := generatedN (GeneratedCutoff.cutoffLog p.degree p.deletion)
  have hZ : 1≤Z := by dsimp[Z];omega
  have hg := EncodedGraph.encode_length_lower g
  have hf : floor≤Z := by dsimp[Z];rw[input_length];omega
  have hnZ : g.vertices≤Z := by dsimp[Z];rw[input_length];omega
  have hB : B≤B*Z := by simpa using Nat.mul_le_mul_left B hZ
  have hmax : max (max floor g.vertices) B≤(B+1)*Z := by
    apply max_le
    · exact (max_le hf hnZ).trans (by nlinarith)
    · nlinarith
  exact (publicLogFrom_dyadic_bound p floor g.vertices g.edges.length hn hlow hdegree).trans
    (by simpa only [dyadicCoefficient,B,Z,Nat.mul_assoc] using Nat.mul_le_mul_left 2 hmax)

def machine (p : SourceConstants) := BitMachineComposition.composition
  (V40GraphSelectedPacket.machine p) D22PostSearchCompiler.machine
def coefficient (p : SourceConstants) := V40ConstructorComposition.coefficient
  (V40GraphSelectedPacket.coefficient p) (V40GraphSelectedPacket.degree p)
  D22PostSearchCompiler.clockCoefficient D22PostSearchCompiler.clockDegree
  (V40GraphSelectedPacket.machine p).pushBound (dyadicCoefficient p)
def degree (p : SourceConstants) := V40ConstructorComposition.degree
  (V40GraphSelectedPacket.degree p) D22PostSearchCompiler.clockDegree

/-- The literal graph bytes, original floor and rounds produce all twelve
public/source scalar fields. Every selected parameter is physically computed. -/
theorem outputs (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid)
    (floor K : Nat) (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :
    let L := publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree
    (machine p).OutputsWithin (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K)
      (D22PostSearchPacket.output (EncodedGraph.encode g) g.vertices g.edges.length L K)
      (coefficient p*((V40GraphConstructorFront.input (EncodedGraph.encode g) floor K).length+1)^degree p) := by
  let L := publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree
  have hs := V40GraphSelectedPacket.outputs p g hg floor K hn hlow hdegree
  have hp := D22PostSearchCompiler.outputs (EncodedGraph.encode g) g.vertices g.edges.length L K
  change D22PostSearchCompiler.machine.OutputsWithin
    (V40GraphConstructorFront.parameterWord g L K)
    (D22PostSearchPacket.output (EncodedGraph.encode g) g.vertices g.edges.length L K)
    (D22PostSearchCompiler.clockCoefficient*
      (2^L+(V40GraphConstructorFront.parameterWord g L K).length+1)^D22PostSearchCompiler.clockDegree) at hp
  have h := BitMachineComposition.composition_outputsWithin (V40GraphSelectedPacket.machine p)
    D22PostSearchCompiler.machine hs hp
  apply BitMachine.outputsWithin_mono _ h
  exact V40ConstructorComposition.time_bound
    (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K).length
    (V40GraphSelectedPacket.coefficient p) (V40GraphSelectedPacket.degree p)
    D22PostSearchCompiler.clockCoefficient D22PostSearchCompiler.clockDegree
    (V40GraphSelectedPacket.machine p).pushBound (dyadicCoefficient p) (2^L)
    (V40GraphConstructorFront.parameterWord g L K).length
    (dyadic_bound p g floor K hn hlow hdegree)
    (BitMachine.output_length_bound (V40GraphSelectedPacket.machine p) hs)

#print axioms dyadic_bound
#print axioms outputs
end
end CurrentAdditive.V40GraphParameterPrefix
