import CurrentAdditive.V40RawRequestPacket
import CurrentAdditive.V40ClassifierTailClock
import CurrentAdditive.V39PacketClock

namespace CurrentAdditive.V40PermittedRawClassifier
noncomputable section
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768
open Paper2 EthInapproximability.CurrentPaper
open CurrentAdditive.V39PermittedNumericalExtraction CurrentAdditive.V39ActualOutputMajority
open V38Schedule V39PublicSchedule V39FullSampleResources V40RandomPermittedFamily

/-- The complete physical calling law, with only a sufficient independent
tape length as its tape interface. Every run is supplied by the concrete
source sampler, table printer, requester, cutter and classifier programs. -/
def CallingLaw (E : ActualEstimator) : Prop :=
  ∀ (g : EncodedGraph.Graph) (hg : g.Valid) (K : Nat) [NeZero g.vertices]
    (cc δv ζ : ℚ) (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V22RawSamplerJoin.precision g.vertices K)
      (V22RawSamplerJoin.reservation g.vertices K)) (suffix classifierTape : List Bool),
    E.classifier.tapeLength (V40RawRequestPacket.request g hg K cc δv ζ ht bits) ≤
      classifierTape.length →
    (V40RawRequestPacket.classifiedMachine E.classifier).OutputsWithin
      (EncodedComplexity.pair (V40RawRequestPacket.inputWord g K bits suffix) classifierTape)
      (E.classifier.output (V40RawRequestPacket.request g hg K cc δv ζ ht bits)
        (classifierTape.take (E.classifier.tapeLength (V40RawRequestPacket.request g hg K cc δv ζ ht bits))))
      (V40ClassifierTail.afterClock E.classifier (V40RawRequestPacket.inputWord g K bits suffix)
        (V40RawRequestPacket.request g hg K cc δv ζ ht bits) classifierTape
        (V40RawRequestPacket.clock g K (V40RawRequestPacket.inputWord g K bits suffix).length))

/-- One extracted estimator and its single fixed classifier machine serve
every graph, every round, every sampled payload and every valid estimator
tape, including inaccurate outputs. -/
theorem extract_all (A : PermittedEstimator) :
    ∃ E : ActualEstimator,
      E.estimator = A.raw.normalize A.ce A.de ∧ E.value = A.value ∧
      (∀ L k (f : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool),
        E.actualComparison (matrixWord L k f) (numerator L k)) ∧
      (∀ word, E.estimator.tapeLength word = A.raw.tapeLength word) ∧
      (∀ word, ValidTable word → ∀ tape : Fin (A.raw.tapeLength word) → Bool,
        E.estimator.output word (List.ofFn tape) = A.raw.output word (List.ofFn tape)) ∧
      (∀ word, ValidTable word → ∀ P : List Bool → Prop,
        E.estimator.prob word P = A.raw.prob word P) ∧ CallingLaw E := by
  obtain ⟨E,he,hv,hc,hl,ho,hp⟩ := V40RandomPermittedFamily.extract_all A
  refine ⟨E,he,hv,hc,hl,ho,hp,?_⟩
  intro g hg K hn cc δv ζ ht bits suffix classifierTape hlen
  exact V40RawRequestPacket.classified_outputs E.classifier g hg K cc δv ζ ht bits
    suffix classifierTape hlen

theorem actual_request_tape_bound (C : SelectedTape.Algorithm)
    (g : EncodedGraph.Graph) (hg : g.Valid) (K : Nat) [NeZero g.vertices]
    (cc δv ζ : ℚ) (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : RoundedDraw.BitBlocks (V22RawSamplerJoin.precision g.vertices K)
      (V22RawSamplerJoin.reservation g.vertices K)) :
    C.tapeLength (V40RawRequestPacket.request g hg K cc δv ζ ht bits) ≤
      C.cR*(9*sampleSide (Nat.clog 2 g.vertices) K^2+4)^C.dR :=
  V40ClassifierTailClock.tape_length C (Nat.clog 2 g.vertices) K
    (V40RawRequestPacket.matrix g hg K cc δv ζ ht bits)

#print axioms extract_all
#print axioms actual_request_tape_bound
end
end CurrentAdditive.V40PermittedRawClassifier
