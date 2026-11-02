import CurrentAdditive.V42RawRequestPacketTypes
import CurrentAdditive.V39TypedPacket
import CurrentAdditive.V40ClassifierTail

namespace CurrentAdditive.V42RawRequestPacket
noncomputable section
set_option maxHeartbeats 20000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768
open Paper2 Turing EthInapproximability.CurrentPaper
open BitMachineEncoding EncodedCommunication
open V42RuntimeSchedule
local instance : DecidableEq V42RawMidpointRequest.Raw := Classical.decEq _

def graphPort : V42RawMidpointRequest.Stack := .inl V42WRaw.graphPort
def kPort : V42RawMidpointRequest.Stack := .inl V42WRaw.kPort
def tapePort : V42RawMidpointRequest.Stack := .inl V42WRaw.tapePort

theorem graph_ne_k : graphPort ≠ kPort := fun h => V42WRaw.graph_ne_k (Sum.inl.inj h)
theorem graph_ne_tape : graphPort ≠ tapePort := fun h => V42WRaw.graph_ne_tape (Sum.inl.inj h)
theorem k_ne_tape : kPort ≠ tapePort := fun h => V42WRaw.k_ne_tape (Sum.inl.inj h)

theorem initial_only_inputs (graph : List Bool) (K : Nat) (tape : List Bool) :
    V42RawMidpointRequest.initial (V42WRaw.initial (V22PublicRepeat.initial
      (V42RawSamplerJoin.initial graph K tape)))=
      V39ThreePortFrame.inputBank graphPort kPort tapePort graph (List.replicate K true) tape := by
  rw [V42WRaw.initial_only_inputs]
  funext j
  cases j with
  | inl j => simp [V42RawMidpointRequest.initial,V40MidpointAmbient.initial,
      V39ThreePortFrame.inputBank,graphPort,kPort,tapePort]
  | inr j => simp [V42RawMidpointRequest.initial,V40MidpointAmbient.initial,
      V39ThreePortFrame.inputBank,graphPort,kPort,tapePort]

def machine : BitMachine.Machine := V39TypedPacket.framedMachine graphPort kPort tapePort
  graph_ne_k graph_ne_tape k_ne_tape V42RawMidpointRequest.program
  V42RawMidpointRequest.start V42RawMidpointRequest.control V42RawMidpointRequest.outputPort

def clock (g : EncodedGraph.Graph) (K inputLength : Nat) :=
  V39WholeBankPacket.clock
    (V39TypedPacket.finiteProgram graphPort kPort tapePort graph_ne_k graph_ne_tape k_ne_tape
      V42RawMidpointRequest.program) inputLength (V42RawMidpointRequest.clock g K)

def inputWord (g : EncodedGraph.Graph) (K : Nat)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) (suffix : List Bool) :=
  BitMachineBankCodec.encode (fun i => V39ThreePortFrame.inputBank graphPort kPort tapePort
    (EncodedGraph.encode g) (List.replicate K true)
    (RoundedCodeLoop.tapeWord (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K) bits ++ suffix)
    ((V39TypedPacket.number graphPort kPort tapePort graph_ne_k graph_ne_tape k_ne_tape).symm i))

def matrix (g : EncodedGraph.Graph) (hg : g.Valid) (K : Nat) [NeZero g.vertices]
    (cc δv ζ : ℚ) (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) :
    Fin (sampleSide (Nat.clog 2 g.vertices) K) →
      Fin (sampleSide (Nat.clog 2 g.vertices) K) → Bool := fun i j =>
  V39RecursiveTable.matrix (V39EdgeSourceFront.edgeActivity g hg (by
      have h := fullS_ge_256 (Nat.clog 2 g.vertices); omega)
    (V42RawPublicRepeat.repetitions g) (V42RawPublicRepeat.width_eq g cc δv ζ ht)) K
    ((V42WRaw.labels g K cc δv ζ ht bits).1 i) ((V42WRaw.labels g K cc δv ζ ht bits).2 j)

def request (g : EncodedGraph.Graph) (hg : g.Valid) (K : Nat) [NeZero g.vertices]
    (cc δv ζ : ℚ) (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) :=
  natField (2*B (Nat.clog 2 g.vertices) K+K)++
    V42RandomPermittedFamily.matrixWord (Nat.clog 2 g.vertices) K (matrix g hg K cc δv ζ ht bits)

/-- A single fixed physical machine consumes the actual three-word caller
packet and computes its exact retained-field midpoint request. -/
theorem outputs (g : EncodedGraph.Graph) (hg : g.Valid) (K : Nat) [NeZero g.vertices]
    (cc δv ζ : ℚ) (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) (suffix : List Bool) :
    machine.OutputsWithin (inputWord g K bits suffix) (request g hg K cc δv ζ ht bits)
      (clock g K (inputWord g K bits suffix).length) := by
  obtain ⟨t,htime,v,hr⟩ := V42RawMidpointRequest.physical_request_raw g hg K cc δv ζ ht bits suffix
  rw [initial_only_inputs] at hr
  apply V39TypedPacket.framed_outputs_of_run graphPort kPort tapePort
    graph_ne_k graph_ne_tape k_ne_tape V42RawMidpointRequest.program
    V42RawMidpointRequest.start V42RawMidpointRequest.control V42RawMidpointRequest.outputPort
    (V39ThreePortFrame.inputBank graphPort kPort tapePort (EncodedGraph.encode g)
      (List.replicate K true) (RoundedCodeLoop.tapeWord (V42RawSamplerJoin.precision g.vertices K)
        (V42RawSamplerJoin.reservation g.vertices K) bits ++ suffix))
    t (V42RawMidpointRequest.clock g K) _ _ htime hr rfl
  simp only [V42RawMidpointRequest.outputPort,V40MidpointAmbient.final,Function.update_self,
    AFront.Projection.matrixPart_encodeInstance]
  rfl

/-- The construction block remains disjoint while the requester runs; the
actual classifier then consumes its exact selected prefix. There is no
assumed execution, comparison, or probability law in this statement. -/
def classifiedMachine (C : SelectedTape.Algorithm) := V40ClassifierTail.after machine C

theorem classified_outputs (C : SelectedTape.Algorithm)
    (g : EncodedGraph.Graph) (hg : g.Valid) (K : Nat) [NeZero g.vertices]
    (cc δv ζ : ℚ) (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) (suffix classifierTape : List Bool)
    (hc : C.tapeLength (request g hg K cc δv ζ ht bits) ≤ classifierTape.length) :
    (classifiedMachine C).OutputsWithin
      (EncodedComplexity.pair (inputWord g K bits suffix) classifierTape)
      (C.output (request g hg K cc δv ζ ht bits)
        (classifierTape.take (C.tapeLength (request g hg K cc δv ζ ht bits))))
      (V40ClassifierTail.afterClock C (inputWord g K bits suffix)
        (request g hg K cc δv ζ ht bits) classifierTape
        (clock g K (inputWord g K bits suffix).length)) :=
  V40ClassifierTail.outputs_after machine C _ _ _ _ (outputs g hg K cc δv ζ ht bits suffix) hc

#print axioms initial_only_inputs
#print axioms outputs
#print axioms classified_outputs
end
end CurrentAdditive.V42RawRequestPacket

