import CurrentAdditive.V42RawRequestPacket
import CurrentAdditive.V40PermittedRawClassifier
import CurrentAdditive.V39PacketClock

namespace CurrentAdditive.V42RawClassifierClock
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768
open Paper2 EthInapproximability.CurrentPaper
open V42RuntimeSchedule
local instance : DecidableEq V42RawMidpointRequest.Raw := Classical.decEq _

def finiteProgram := V39TypedPacket.finiteProgram
  V42RawRequestPacket.graphPort V42RawRequestPacket.kPort V42RawRequestPacket.tapePort
  V42RawRequestPacket.graph_ne_k V42RawRequestPacket.graph_ne_tape V42RawRequestPacket.k_ne_tape
  V42RawMidpointRequest.program

def packetCoefficient := V39WholeBankPacket.clock finiteProgram 1 1

theorem packet_linear (g : EncodedGraph.Graph) (K inputLength : Nat) :
    V42RawRequestPacket.clock g K inputLength ≤
      packetCoefficient*(inputLength+V42RawMidpointRequest.clock g K+1) :=
  V39WholeBankPacket.clock_linear finiteProgram inputLength (V42RawMidpointRequest.clock g K)

theorem requester_cap_mono {a b : Nat} (h : a≤b) :
    V40MidpointRequest.cap a≤V40MidpointRequest.cap b := by
  unfold V40MidpointRequest.cap V40MidpointRequest.invokeCap
  gcongr

/-- One polynomial in the physical input size, raw sampler/printer time,
actual table entries and bounded independent classifier block pays every
requester, bank wrapper, transfer, tape cut and classifier transition. -/
def cap (C : SelectedTape.Algorithm) (X : Nat) :=
  58*X+28+packetCoefficient*(2*X+V40MidpointRequest.cap X+2)+
    V40ClassifierTail.cap C (19*X+7)

theorem cap_poly (C : SelectedTape.Algorithm) : Unit4Shell.Poly.PolyIn id (cap C) := by
  unfold cap V40MidpointRequest.cap V40MidpointRequest.invokeCap
    V40ClassifierTail.cap NPOwner1.Trunc.timeBound
  repeat (first
    | exact Unit4Shell.Poly.self
    | exact Unit4Shell.Poly.const _
    | apply Unit4Shell.Poly.add
    | apply Unit4Shell.Poly.mul
    | apply Unit4Shell.Poly.pow)

theorem classified_clock_le (C : SelectedTape.Algorithm)
    (g : EncodedGraph.Graph) (hg : g.Valid) (K : Nat) [NeZero g.vertices]
    (cc δv ζ : ℚ) (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) (suffix classifierTape : List Bool) :
    V40ClassifierTail.afterClock C (V42RawRequestPacket.inputWord g K bits suffix)
      (V42RawRequestPacket.request g hg K cc δv ζ ht bits) classifierTape
      (V42RawRequestPacket.clock g K (V42RawRequestPacket.inputWord g K bits suffix).length) ≤
    cap C ((V42RawRequestPacket.inputWord g K bits suffix).length+V42WRaw.clock g K+
      sampleSide (Nat.clog 2 g.vertices) K^2+classifierTape.length+1) := by
  let input := V42RawRequestPacket.inputWord g K bits suffix
  let request := V42RawRequestPacket.request g hg K cc δv ζ ht bits
  let T := sampleSide (Nat.clog 2 g.vertices) K^2
  let X := input.length+V42WRaw.clock g K+T+classifierTape.length+1
  have hi : input.length≤X := by dsimp [X]; omega
  have hr : V42WRaw.clock g K≤X := by dsimp [X]; omega
  have hT : T≤X := by dsimp [X]; omega
  have htape : classifierTape.length≤X := by dsimp [X]; omega
  have hrequest0 := V40MidpointRequest.v42_request_length (Nat.clog 2 g.vertices) K
    (V42RawRequestPacket.matrix g hg K cc δv ζ ht bits)
  have hrequest : request.length≤9*X+3 := by
    change request.length≤9*T+3 at hrequest0
    omega
  have hpacket0 := packet_linear g K input.length
  have hpacket : V42RawRequestPacket.clock g K input.length ≤
      packetCoefficient*(2*X+V40MidpointRequest.cap X+2) := by
    apply hpacket0.trans
    have hc := requester_cap_mono hT
    unfold V42RawMidpointRequest.clock at *
    change packetCoefficient*(input.length+(V42WRaw.clock g K+V40MidpointRequest.cap T+1)+1)≤_
    exact Nat.mul_le_mul_left packetCoefficient (by omega)
  have hpair : (EncodedComplexity.pair request classifierTape).length≤19*X+7 := by
    rw [EncodedComplexity.pair_length]
    omega
  have hcap := V40ClassifierTailClock.cap_mono C hpair
  change V40ClassifierTail.afterClock C input request classifierTape
    (V42RawRequestPacket.clock g K input.length) ≤ cap C X
  unfold V40ClassifierTail.afterClock cap
  omega

/-- Constants depend only on the fixed permitted classifier and fixed
programs; they precede every source graph, round and random tape. -/
theorem uniform_polynomial (C : SelectedTape.Algorithm) :
    ∃ c d : Nat, ∀ (g : EncodedGraph.Graph) (hg : g.Valid) (K : Nat) [NeZero g.vertices]
      (cc δv ζ : ℚ) (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
      (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
        (V42RawSamplerJoin.reservation g.vertices K)) (suffix classifierTape : List Bool),
      V40ClassifierTail.afterClock C (V42RawRequestPacket.inputWord g K bits suffix)
        (V42RawRequestPacket.request g hg K cc δv ζ ht bits) classifierTape
        (V42RawRequestPacket.clock g K (V42RawRequestPacket.inputWord g K bits suffix).length) ≤
      c*((V42RawRequestPacket.inputWord g K bits suffix).length+V42WRaw.clock g K+
        sampleSide (Nat.clog 2 g.vertices) K^2+classifierTape.length+1+1)^d := by
  obtain ⟨c,d,h⟩ := cap_poly C
  refine ⟨c,d,?_⟩
  intro g hg K hn cc δv ζ ht bits suffix classifierTape
  exact (classified_clock_le C g hg K cc δv ζ ht bits suffix classifierTape).trans (h _)

#print axioms packet_linear
#print axioms classified_clock_le
#print axioms cap_poly
#print axioms uniform_polynomial
end
end CurrentAdditive.V42RawClassifierClock

