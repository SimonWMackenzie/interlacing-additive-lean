import CurrentAdditive.V42RawRequestPacket
import CurrentAdditive.V42WRawPacket
import CurrentAdditive.V42JointEstimatorLaw

/-! Literal identities from the physical row-major table to the permitted
estimator request. These hold on every rounded random tape, including every
fallback and default-label outcome. They assume no communication gap. -/
namespace CurrentAdditive.V42RawRequestSemantics
open Paper2 EthInapproximability.CurrentPaper V42RuntimeSchedule
open V39ActualOutputMajority
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768
variable (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
variable (K : ℕ) (cc δv ζ : ℚ)
variable (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)

theorem printed_word_eq
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) :
    V42WRaw.outputWord g hg K cc δv ζ ht bits=
      EncodedCommunication.encodeInstance (V42RandomPermittedFamily.instanceWord (Nat.clog 2 g.vertices) K
        (V42RawRequestPacket.matrix g hg K cc δv ζ ht bits)) := rfl

theorem request_eq
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) :
    V42RawRequestPacket.request g hg K cc δv ζ ht bits=
      V42JointEstimatorLaw.request (Nat.clog 2 g.vertices) K
        (V42RawRequestPacket.matrix g hg K cc δv ζ ht bits) := rfl

theorem request_physical_projection
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) :
    V42RawRequestPacket.request g hg K cc δv ζ ht bits=
      EncodedCommunication.natField (2*B (Nat.clog 2 g.vertices) K+K)++
        AFront.Projection.matrixPart (V42WRaw.outputWord g hg K cc δv ζ ht bits) := by
  rw [printed_word_eq,AFront.Projection.matrixPart_encodeInstance]
  rfl

theorem classifier_length (E : ActualEstimator)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision g.vertices K)
      (V42RawSamplerJoin.reservation g.vertices K)) :
    E.classifier.tapeLength (V42RawRequestPacket.request g hg K cc δv ζ ht bits)=
      V42JointEstimatorLaw.classifierLength E (Nat.clog 2 g.vertices) K :=
  V42JointEstimatorLaw.classifier_length E (Nat.clog 2 g.vertices) K _

#print axioms printed_word_eq
#print axioms request_physical_projection
#print axioms classifier_length
end
end CurrentAdditive.V42RawRequestSemantics
