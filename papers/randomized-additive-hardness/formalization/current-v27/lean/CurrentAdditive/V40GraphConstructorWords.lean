import CurrentAdditive.V40GraphEndpointIdentity
import CurrentAdditive.V40StoredEnvelope
import CurrentAdditive.D22PostSearchPacket
import CurrentAdditive.StoredStepContext

namespace CurrentAdditive.V40GraphConstructorWords
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction V38Schedule

def law (g : EncodedGraph.Graph) (L : Nat) (hs : 4≤generatedS L) (hn : 0<g.vertices) :=
  LiteralEdgeEncoder.indexedItemLaw (generatedS L) g.vertices hs hn

def activity (g : EncodedGraph.Graph) (hg : g.Valid) (L : Nat) (hs : 4≤generatedS L)
    (hq : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) g.edges.length
      (publicRepetition L g.edges.length)) :
    Fin (4*generatedS L*(g.vertices+(generatedS L-3))) →
      Fin (generatedQ₂ L) → Option (Fin (generatedS L)) := by
  haveI : NeZero (generatedS L) := ⟨by omega⟩
  exact graphActivity (by omega) hq (LiteralEdgeEncoder.edge g hg)

def context (g : EncodedGraph.Graph) (hg : g.Valid) (L : Nat) (hs : 4≤generatedS L)
    (hn : 0<g.vertices)
    (hq : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) g.edges.length
      (publicRepetition L g.edges.length)) :=
  StoredStepContext.context (generatedQ₁ L) (generatedW L) (generatedQ L)
    (law g L hs hn) (activity g hg L hs hq)

theorem context_eq (g : EncodedGraph.Graph) (hg : g.Valid) (L : Nat) (hs : 4≤generatedS L)
    (hn : 0<g.vertices)
    (hq : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) g.edges.length
      (publicRepetition L g.edges.length)) :
    context g hg L hs hn hq=D22PostSearchPacket.stepContext L
      (StoredWeightedState.lawBytes (law g L hs hn))
      (StoredStepContext.activityWords (activity g hg L hs hq)) := rfl

def source (g : EncodedGraph.Graph) (hg : g.Valid) (L K : Nat) (hs : 4≤generatedS L)
    (hn : 0<g.vertices)
    (hq : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) g.edges.length
      (publicRepetition L g.edges.length)) :=
  D22PostSearchPacket.withSource (EncodedGraph.encode g) g.vertices g.edges.length L K
    (StoredWeightedState.lawBytes (law g L hs hn))
    (StoredStepContext.activityWords (activity g hg L hs hq))

def run (g : EncodedGraph.Graph) (hg : g.Valid) (L : Nat) (hs : 4≤generatedS L)
    (hn : 0<g.vertices)
    (hq : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) g.edges.length
      (publicRepetition L g.edges.length)) (j : Nat) : StoredMatrix := by
  haveI : NeZero (generatedS L) := ⟨by omega⟩
  haveI : NeZero (generatedQ₂ L) := ⟨by unfold generatedQ₂ generatedN;positivity⟩
  haveI : NeZero (generatedW L) := ⟨by unfold generatedW generatedN;positivity⟩
  haveI : NeZero (generatedQ L) := ⟨by unfold generatedQ generatedN;positivity⟩
  exact graphRun (w:=generatedW L) (Q:=generatedQ L) hs hn hq (LiteralEdgeEncoder.edge g hg) L j

def word (g : EncodedGraph.Graph) (hg : g.Valid) (L K : Nat) (hs : 4≤generatedS L)
    (hn : 0<g.vertices)
    (hq : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) g.edges.length
      (publicRepetition L g.edges.length)) (j : Nat) :=
  V40StoredEnvelope.input L K (context g hg L hs hn hq) (run g hg L hs hn hq j)

def step (g : EncodedGraph.Graph) (hg : g.Valid) (L : Nat) (hs : 4≤generatedS L)
    (hn : 0<g.vertices)
    (hq : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) g.edges.length
      (publicRepetition L g.edges.length)) (R : StoredMatrix) : StoredMatrix := by
  haveI : NeZero (generatedS L) := ⟨by omega⟩
  haveI : NeZero (generatedQ₁ L) := ⟨by unfold generatedQ₁;omega⟩
  haveI : NeZero (generatedQ₂ L) := ⟨by unfold generatedQ₂ generatedN;positivity⟩
  haveI : NeZero (generatedW L) := ⟨by unfold generatedW generatedN;positivity⟩
  haveI : NeZero (generatedQ L) := ⟨by unfold generatedQ generatedN;positivity⟩
  exact StoredMatrix.step (q₁:=generatedQ₁ L) (s:=generatedS L) (w:=generatedW L) (Q:=generatedQ L)
    (law g L hs hn) (activity g hg L hs hq) R

theorem run_zero (g : EncodedGraph.Graph) (hg : g.Valid) (L : Nat) (hs : 4≤generatedS L)
    (hn : 0<g.vertices)
    (hq : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) g.edges.length
      (publicRepetition L g.edges.length)) : run g hg L hs hn hq 0=storedLookupSeed L := rfl

theorem run_succ (g : EncodedGraph.Graph) (hg : g.Valid) (L : Nat) (hs : 4≤generatedS L)
    (hn : 0<g.vertices)
    (hq : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) g.edges.length
      (publicRepetition L g.edges.length)) (j : Nat) :
    run g hg L hs hn hq (j+1)=step g hg L hs hn hq (run g hg L hs hn hq j) := rfl

/-- Every already admissible supplied dyadic order is selected exactly.
Earlier failed candidates and sufficient large cutoffs play no role here. -/
theorem publicLogFrom_eq_dyadic (p : SourceConstants) (n m L : Nat)
    (hn : 0<n) (hlow : n≤2*m) (hdegree : 2*m≤p.degree*n) (hnN : n≤2^L)
    (ht : GeneratedTests p.deletion L m (sourceDeltaV p.gamma p.degree n m) (sourceZeta p.gamma)) :
    publicLogFrom p (2^L) n m hn hlow hdegree=L := by
  have hclog : Nat.clog 2 (max (2^L) n)=L := by
    rw [max_eq_left hnN,Nat.clog_pow 2 L (by decide)]
  apply le_antisymm
  · change Nat.find (exists_passing_from p (2^L) n m hn hlow hdegree)≤L
    exact Nat.find_min' _ ⟨by rw[hclog],ht⟩
  · simpa only [hclog] using (publicLogFrom_spec p (2^L) n m hn hlow hdegree).1

/-- The literal source-law/activity order and the retained public parameters
instantiate the exact current public graph construction. -/
theorem run_public (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid) (floor j : Nat)
    (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :
    let L := publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree
    let ht := (publicLogFrom_spec p floor g.vertices g.edges.length hn hlow hdegree).2
    run g hg L (passing_s_ge_four _ _ _ _ _ ht) hn (passing_repetition_eq _ _ _ _ _ ht) j=
      publicGraphRunFrom p floor hn hlow hdegree (Paper2.CanonicalEdgeTape.graphEdge g hg) j := by
  dsimp only
  rw [← V40GraphEndpointIdentity.edge_eq g hg]
  rfl

#print axioms context_eq
#print axioms run_zero
#print axioms run_succ
#print axioms publicLogFrom_eq_dyadic
#print axioms run_public
end
end CurrentAdditive.V40GraphConstructorWords
