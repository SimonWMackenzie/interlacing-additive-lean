import CurrentAdditive.V39TypedPacket
import CurrentAdditive.V42WRawRun
import CurrentAdditive.V42WRawInitial
import Paper2.A3LSucc

/-! One fixed packed-input machine prints the exact current encoded square
table from only graph bytes, unary K, and its actual rounded random tape. -/
namespace CurrentAdditive.V42WRaw
noncomputable section
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768
open Paper2 Turing EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding EncodedCommunication
open V42RuntimeSchedule
local instance rawPacketStackDecEq : DecidableEq Stack := Classical.decEq _

def packetLabelType {S L V : Type} (_ : L → TM2.Stmt (fun _ : S => Bool) L V) : Type := L
def packetControlType {S L V : Type} (_ : L → TM2.Stmt (fun _ : S => Bool) L V) : Type := V
abbrev PacketLabel := packetLabelType program
abbrev PacketControl := packetControlType program
instance rawPacketStackFintype : Fintype Stack := by infer_instance
instance rawPacketLabelFintype : Fintype PacketLabel := by
  unfold PacketLabel packetLabelType
  infer_instance
instance rawPacketControlFintype : Fintype PacketControl := by
  unfold PacketControl packetControlType
  infer_instance

def finiteMachine : BitMachine.Machine :=
  V39TypedPacket.machine graphPort kPort tapePort graph_ne_k graph_ne_tape k_ne_tape
    program start control outputPort

def packetClock (inputLength time : Nat) :=
  V39TypedPacket.clock graphPort kPort tapePort graph_ne_k graph_ne_tape k_ne_tape
    program inputLength time

def payload (g : EncodedGraph.Graph) (hg : g.Valid) (K : Nat) [NeZero g.vertices]
    (cc δv ζ : ℚ) (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) : List Bool :=
  let z := labels g K cc δv ζ ht bits
  let m := sampleSide (Nat.clog 2 g.vertices) K
  MatrixMaterialization.rowMajor (fun i j : Fin m =>
    V39RecursiveTable.matrix (V39EdgeSourceFront.edgeActivity g hg
      (by have h := fullS_ge_256 (Nat.clog 2 g.vertices); omega)
      (V42RawPublicRepeat.repetitions g) (V42RawPublicRepeat.width_eq g cc δv ζ ht))
      K (z.1 i) (z.2 j))

def outputWord (g : EncodedGraph.Graph) (hg : g.Valid) (K : Nat) [NeZero g.vertices]
    (cc δv ζ : ℚ) (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) : List Bool :=
  encodeInstance ⟨sampleSide (Nat.clog 2 g.vertices) K,sampleSide (Nat.clog 2 g.vertices) K,
    B (Nat.clog 2 g.vertices) K,payload g hg K cc δv ζ ht bits⟩

theorem packet_outputs (g : EncodedGraph.Graph) (hg : g.Valid) (K : Nat)
    [NeZero g.vertices] (cc δv ζ : ℚ)
    (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) (suffix : List Bool) :
    let tape := RoundedCodeLoop.tapeWord (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K) bits ++ suffix
    let input := BitMachineBankCodec.encode ![EncodedGraph.encode g,List.replicate K true,tape]
    finiteMachine.OutputsWithin input (outputWord g hg K cc δv ζ ht bits)
      (packetClock input.length (clock g K)) := by
  intro tape input
  obtain ⟨t,htime,v,hr⟩ := physical_encoded_raw g hg K cc δv ζ ht bits suffix
  apply V39TypedPacket.outputs_of_run graphPort kPort tapePort graph_ne_k graph_ne_tape k_ne_tape
    program start control outputPort (EncodedGraph.encode g) (List.replicate K true) tape
    t (clock g K) ⟨none,v,_⟩ (outputWord g hg K cc δv ζ ht bits) htime
  · simpa only [initial_only_inputs] using hr
  · rfl
  · exact V39WEncodedTable.embedded_final_word printerSlots _ _ _ _ _ _ _

#print axioms packet_outputs
end
end CurrentAdditive.V42WRaw

