import CurrentAdditive.V40BlockTapeLaw
import CurrentAdditive.V40RawRequestPacket

set_option autoImplicit false

/-! The actual raw-input request machine and the proved same-word probability
consumer have the identical indexed matrix and midpoint request. This is a
semantic equality join; the physical caller and its clocks stay with their
defining owner. -/

namespace CurrentAdditive.V40RawRequestSemantics
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open V38Schedule V39PublicSchedule V39FullSampleResources
open V39ActualRandomizedReduction V39ActualOutputMajority
open V40RandomPermittedFamily V40JointEstimatorLaw V40PhysicalEstimatorConsumer
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768

variable (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
variable (K : ℕ) (cc δv ζ : ℚ)
variable (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)

theorem table_eq (hN : Reservation (Nat.clog 2 g.vertices) K)
    (bits : Bits g.vertices (Nat.clog 2 g.vertices) K) :
    V40RawRequestPacket.matrix g hg K cc δv ζ ht bits=
      table g hg (Nat.clog 2 g.vertices) (V22RawPublicRepeat.repetitions g)
        (V22RawPublicRepeat.width_eq g cc δv ζ ht) K hN bits := by
  rfl

theorem request_eq (hN : Reservation (Nat.clog 2 g.vertices) K)
    (bits : Bits g.vertices (Nat.clog 2 g.vertices) K) :
    V40RawRequestPacket.request g hg K cc δv ζ ht bits=
      request (Nat.clog 2 g.vertices) K
        (table g hg (Nat.clog 2 g.vertices) (V22RawPublicRepeat.repetitions g)
          (V22RawPublicRepeat.width_eq g cc δv ζ ht) K hN bits) := by
  rfl

theorem request_physical_projection (hN : Reservation (Nat.clog 2 g.vertices) K)
    (bits : Bits g.vertices (Nat.clog 2 g.vertices) K) :
    V40RawRequestPacket.request g hg K cc δv ζ ht bits=
      EncodedCommunication.natField (2*B (Nat.clog 2 g.vertices) K+K)++
        AFront.Projection.matrixPart (physicalWord g hg (Nat.clog 2 g.vertices)
          (V22RawPublicRepeat.repetitions g) (V22RawPublicRepeat.width_eq g cc δv ζ ht)
          K hN bits) := by
  rw [V40PhysicalEstimatorConsumer.projected_word]
  rfl

def accepts (E : ActualEstimator) (bits : Bits g.vertices (Nat.clog 2 g.vertices) K)
    (t : Fin (classifierLength E (Nat.clog 2 g.vertices) K) → Bool) : Prop :=
  E.classifier.output (V40RawRequestPacket.request g hg K cc δv ζ ht bits)
    (List.ofFn t)=[true]

theorem accepts_eq (E : ActualEstimator) (hN : Reservation (Nat.clog 2 g.vertices) K)
    (bits : Bits g.vertices (Nat.clog 2 g.vertices) K)
    (t : Fin (classifierLength E (Nat.clog 2 g.vertices) K) → Bool) :
    accepts g hg K cc δv ζ ht E bits t ↔
      V40PhysicalEstimatorConsumer.accepts g hg (Nat.clog 2 g.vertices)
        (V22RawPublicRepeat.repetitions g) (V22RawPublicRepeat.width_eq g cc δv ζ ht)
        E K hN bits t := by
  unfold accepts V40PhysicalEstimatorConsumer.accepts
  rw [request_physical_projection g hg K cc δv ζ ht hN bits]
  rfl

theorem classifier_length (E : ActualEstimator)
    (bits : Bits g.vertices (Nat.clog 2 g.vertices) K) :
    E.classifier.tapeLength (V40RawRequestPacket.request g hg K cc δv ζ ht bits)=
      classifierLength E (Nat.clog 2 g.vertices) K := by
  rw [request_eq g hg K cc δv ζ ht (fullDrawCap_le cc _ _ K δv ζ ht) bits]
  exact V40JointEstimatorLaw.classifier_length _ _ _ _

theorem source_yes (Δ : ℕ) (hΔ : 0<Δ) (γ : ℚ) (hγ : 0<γ)
    (hnm : g.vertices≤2*g.edges.length) (hdeg : 2*g.edges.length≤Δ*g.vertices)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ≤g.vertices)
    (E : ActualEstimator) (u : ℝ) (hu : 0≤u) (hgap : 2*u<(K:ℝ))
    (hcompare : ∀ f : Table (Nat.clog 2 g.vertices) K,
      E.actualComparison (matrixWord (Nat.clog 2 g.vertices) K f)
        (numerator (Nat.clog 2 g.vertices) K))
    (haccurate : Accurate E (Nat.clog 2 g.vertices) K u)
    (colour : Fin g.vertices → Fin 3)
    (proper : ∀ e, colour (LiteralEdgeEncoder.edge g hg e false)≠colour (LiteralEdgeEncoder.edge g hg e true)) :
    (99:ℝ)/100≤(jointLaw E g.vertices (Nat.clog 2 g.vertices) K).prob
      (fun z => accepts g hg K cc δv ζ ht E z.1 z.2) := by
  let hN:=source_reservation g (Nat.clog 2 g.vertices) rfl Δ hΔ γ hγ hnm hdeg hlarge K
  simp_rw [accepts_eq g hg K cc δv ζ ht E hN]
  exact V40PhysicalEstimatorConsumer.source_yes g hg (Nat.clog 2 g.vertices)
    (V22RawPublicRepeat.repetitions g) (V22RawPublicRepeat.width_eq g cc δv ζ ht)
    rfl Δ hΔ γ hγ hnm hdeg hlarge E K u hu hgap hcompare haccurate colour proper

theorem source_no (Δ : ℕ) (hΔ : 0<Δ)
    (hdegree : ∀ v, SourceItems.degree (LiteralEdgeEncoder.edge g hg) v≤Δ)
    (γ : ℚ) (hγ : 0<γ) (hnm : g.vertices≤2*g.edges.length)
    (hdeg : 2*g.edges.length≤Δ*g.vertices)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ≤g.vertices)
    (gap : ∀ colour : Fin g.vertices → Fin 3, (γ:ℝ)*g.edges.length≤
      ((Finset.univ.filter (fun e => colour (LiteralEdgeEncoder.edge g hg e false)=
        colour (LiteralEdgeEncoder.edge g hg e true))).card:ℝ))
    (E : ActualEstimator) (u : ℝ) (hu : 0≤u) (hgap : 2*u<(K:ℝ))
    (hcompare : ∀ f : Table (Nat.clog 2 g.vertices) K,
      E.actualComparison (matrixWord (Nat.clog 2 g.vertices) K f)
        (numerator (Nat.clog 2 g.vertices) K))
    (haccurate : Accurate E (Nat.clog 2 g.vertices) K u) :
    (jointLaw E g.vertices (Nat.clog 2 g.vertices) K).prob
      (fun z => accepts g hg K cc δv ζ ht E z.1 z.2)≤(3:ℝ)/100 := by
  let hN:=source_reservation g (Nat.clog 2 g.vertices) rfl Δ hΔ γ hγ hnm hdeg hlarge K
  simp_rw [accepts_eq g hg K cc δv ζ ht E hN]
  exact V40PhysicalEstimatorConsumer.source_no g hg (Nat.clog 2 g.vertices)
    (V22RawPublicRepeat.repetitions g) (V22RawPublicRepeat.width_eq g cc δv ζ ht)
    rfl Δ hΔ hdegree γ hγ hnm hdeg hlarge gap E K u hu hgap hcompare haccurate

#print axioms table_eq
#print axioms request_eq
#print axioms request_physical_projection
#print axioms source_yes
#print axioms source_no
end
end CurrentAdditive.V40RawRequestSemantics
