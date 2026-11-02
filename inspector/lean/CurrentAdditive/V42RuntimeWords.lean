import CurrentAdditive.V42GeneratedConstruction
import CurrentAdditive.V42RuntimeSource
import CurrentAdditive.StoredMatrixEnvelopeStep
import CurrentAdditive.V40StoredEnvelope

/-! Identity of every physical round with the actual v42 graph construction.
The graph bytes generate the item law and activity table in the same order
used by the seven Code D calls and the final printed matrix. -/
namespace CurrentAdditive.V42RuntimeWords
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction V42Schedule
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

def law (g : EncodedGraph.Graph) (k : ℕ) (hk : 2≤k) (hn : 0<g.vertices) :=
  LiteralEdgeEncoder.indexedItemLaw (s k) g.vertices (V42GeneratedConstruction.s_ge_four k hk) hn
def activity (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (hk : 2≤k)
    (hq : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) g.edges.length
      (V42RuntimePacket.repetition k g.edges.length)) :
    Fin (4*s k*(g.vertices+(s k-3))) → Fin (q₂ k (4*k)) → Option (Fin (s k)) := by
  haveI : NeZero (s k) := ⟨(s_pos k).ne'⟩
  exact graphActivity (by have h:=V42GeneratedConstruction.s_ge_four k hk;omega) hq (LiteralEdgeEncoder.edge g hg)
def context (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (hk : 2≤k) (hn : 0<g.vertices)
    (hq : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) g.edges.length
      (V42RuntimePacket.repetition k g.edges.length)) :=
  StoredStepContext.context (q₁ k) (w k) (Q k) (law g k hk hn) (activity g hg k hk hq)
def source (g : EncodedGraph.Graph) (hg : g.Valid) (k K : ℕ) (hk : 2≤k) (hn : 0<g.vertices)
    (hq : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) g.edges.length
      (V42RuntimePacket.repetition k g.edges.length)) :=
  V42RuntimePacket.withSource (EncodedGraph.encode g) g.vertices g.edges.length k K
    (StoredWeightedState.lawBytes (law g k hk hn))
    (StoredStepContext.activityWords (activity g hg k hk hq))
def run (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (hk : 2≤k) (hn : 0<g.vertices)
    (hq : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) g.edges.length
      (V42RuntimePacket.repetition k g.edges.length)) (j : ℕ) : StoredMatrix :=
  V42GeneratedConstruction.graphRun k (4*k) hk hn hq (LiteralEdgeEncoder.edge g hg) (4*k) j
def word (g : EncodedGraph.Graph) (hg : g.Valid) (k K : ℕ) (hk : 2≤k) (hn : 0<g.vertices)
    (hq : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) g.edges.length
      (V42RuntimePacket.repetition k g.edges.length)) (j : ℕ) :=
  V40StoredEnvelope.input (4*k) K (context g hg k hk hn hq) (run g hg k hk hn hq j)
def data (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (hk : 2≤k) (hn : 0<g.vertices)
    (hq : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) g.edges.length
      (V42RuntimePacket.repetition k g.edges.length)) (R : StoredMatrix) : StoredRoundData.Data where
  parameters := {
    q₁ := q₁ k
    q₂ := q₂ k (4*k)
    s := s k
    w := w k
    Q := Q k
    ni := 4*s k*(g.vertices+(s k-3))
    hq₁ := by have h:=V42GeneratedConstruction.s_ge_four k hk;unfold q₁;omega
    hq₂ := q₂_pos k (4*k)
    hs := s_pos k
    hw := w_pos k
    hQ := Q_pos k
    μI := law g k hk hn
    R := R }
  activity := activity g hg k hk hq

theorem run_zero (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (hk : 2≤k) (hn : 0<g.vertices)
    (hq : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) g.edges.length
      (V42RuntimePacket.repetition k g.edges.length)) :
    run g hg k hk hn hq 0=storedLookupSeed (4*k) := rfl

theorem context_eq (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (hk : 2≤k) (hn : 0<g.vertices)
    (hq : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) g.edges.length
      (V42RuntimePacket.repetition k g.edges.length)) :
    context g hg k hk hn hq=V42RuntimePacket.context k
      (StoredWeightedState.lawBytes (law g k hk hn))
      (StoredStepContext.activityWords (activity g hg k hk hq)) := rfl

theorem round_outputs (g : EncodedGraph.Graph) (hg : g.Valid) (k K : ℕ) (hk : 2≤k) (hn : 0<g.vertices)
    (hq : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) g.edges.length
      (V42RuntimePacket.repetition k g.edges.length)) (j : ℕ) :
    StoredMatrixEnvelopeStep.machine.OutputsWithin (word g hg k K hk hn hq j)
      (word g hg k K hk hn hq (j+1))
      (StoredMatrixEnvelopeStep.coefficient*((word g hg k K hk hn hq j).length+1)^StoredMatrixEnvelopeStep.degree) := by
  exact StoredMatrixEnvelopeStep.outputs (data g hg k hk hn hq (run g hg k hk hn hq j)) (4*k) K

theorem source_outputs (g : EncodedGraph.Graph) (hg : g.Valid) (k K : ℕ) (hk : 2≤k) (hn : 0<g.vertices)
    (hq : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) g.edges.length
      (V42RuntimePacket.repetition k g.edges.length)) :
    V42RuntimeSource.machine.OutputsWithin
      (V42RuntimePacket.output (EncodedGraph.encode g) g.vertices g.edges.length k K)
      (source g hg k K hk hn hq)
      (V42RuntimeSource.coefficient*
        ((V42RuntimePacket.output (EncodedGraph.encode g) g.vertices g.edges.length k K).length+1)^V42RuntimeSource.degree) := by
  haveI : NeZero (s k) := ⟨(s_pos k).ne'⟩
  exact V42RuntimeSource.outputs g hg k K hn (V42GeneratedConstruction.s_ge_four k hk) hq

#print axioms round_outputs
#print axioms source_outputs
end
end CurrentAdditive.V42RuntimeWords
