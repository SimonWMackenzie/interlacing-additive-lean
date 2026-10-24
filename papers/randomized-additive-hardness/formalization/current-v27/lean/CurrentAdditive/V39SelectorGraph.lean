import CurrentAdditive.V39SelectorConsequences
import CurrentAdditive.V39EdgeSourceFront
import CurrentAdditive.EdgeMatrixProductionConjugacy

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192

namespace CurrentAdditive.V39SelectorTransport
noncomputable section
open Paper2 SourceCoordinateConjugacy V39RecursiveGenerator
open EthInapproximability.CurrentPaper
open Workspace.Types.CommComplexity Paper2.RankLeaves

variable {p q₁ q₂ s w Q : ℕ} [NeZero s]

noncomputable def graphPermutation (g : EncodedGraph.Graph) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r) : Fin q₂ ≃ Fin q₂ :=
  (finCongr hq).trans ((LiteralEdgeEncoder.selectorPermutation s g.edges.length r).trans
    (finCongr hq).symm)

def ownerActivity (g : EncodedGraph.Graph) (hg : g.Valid) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r) :=
  EdgeSourceMatrix.activity (LiteralEdgeEncoder.itemOrder s g.vertices)
    (LiteralEdgeEncoder.edge g hg) hs r hq

/-- The executable graph activity is the owner's activity with the literal
selector permutation, including the exact q₂-to-Width cast. -/
theorem graph_activity (g : EncodedGraph.Graph) (hg : g.Valid) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r) :
    V39EdgeSourceFront.edgeActivity g hg hs r hq =
      activityNew (graphPermutation g r hq) (ownerActivity g hg hs r hq) := by
  subst q₂
  simpa [graphPermutation,V39EdgeSourceFront.edgeActivity,ownerActivity] using
    (LiteralEdgeEncoder.activity_eq_owner hs (LiteralEdgeEncoder.edge g hg) (r:=r))

/-- Owner complete labels map bijectively to the actual physical complete
labels, with identical recursive entries at every level. -/
theorem graph_matrix (g : EncodedGraph.Graph) (hg : g.Valid) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r) (k : ℕ)
    (x : Row g.vertices p q₁ q₂ s w Q k) (y : Column g.vertices p q₁ q₂ s w Q k) :
    V39RecursiveTable.matrix (V39EdgeSourceFront.edgeActivity g hg hs r hq) k
      (eR g.vertices p q₁ q₂ s w Q (graphPermutation g r hq) k x)
      (eC g.vertices p q₁ q₂ s w Q (graphPermutation g r hq) k y) =
      V39RecursiveTable.matrix (ownerActivity g hg hs r hq) k x y := by
  rw [graph_activity]
  exact matrix_map _ _ _ _ _

theorem graph_D (g : EncodedGraph.Graph) (hg : g.Valid) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r) (k : ℕ) :
    D (V39RecursiveTable.matrix (p₀:=p) (q₁:=q₁) (w:=w) (Q:=Q)
      (V39EdgeSourceFront.edgeActivity g hg hs r hq) k) =
    D (V39RecursiveTable.matrix (p₀:=p) (q₁:=q₁) (w:=w) (Q:=Q)
      (ownerActivity g hg hs r hq) k) := by
  rw [graph_activity]
  exact D_map _ _ _

theorem graph_rank (g : EncodedGraph.Graph) (hg : g.Valid) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r) (k : ℕ) :
    (realMatrix (V39RecursiveTable.matrix (p₀:=p) (q₁:=q₁) (w:=w) (Q:=Q)
      (V39EdgeSourceFront.edgeActivity g hg hs r hq) k)).rank =
    (realMatrix (V39RecursiveTable.matrix (p₀:=p) (q₁:=q₁) (w:=w) (Q:=Q)
      (ownerActivity g hg hs r hq) k)).rank := by
  rw [graph_activity]
  exact rank_map _ _ _

variable [NeZero p] [NeZero q₁] [NeZero q₂]
  [NeZero (4*s)] [NeZero (s-3)] [NeZero w] [NeZero Q]

theorem graph_laws_pushes (g : EncodedGraph.Graph) [NeZero g.vertices] (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r) (k : ℕ) :
    (laws g.vertices p q₁ q₂ s w Q k).1.toFiniteLaw.PushesTo
      (laws g.vertices p q₁ q₂ s w Q k).1.toFiniteLaw
      (eR g.vertices p q₁ q₂ s w Q (graphPermutation g r hq) k) ∧
    (laws g.vertices p q₁ q₂ s w Q k).2.toFiniteLaw.PushesTo
      (laws g.vertices p q₁ q₂ s w Q k).2.toFiniteLaw
      (eC g.vertices p q₁ q₂ s w Q (graphPermutation g r hq) k) :=
  laws_pushes _ _ _ _ _ _ _ _ _

theorem graph_profile_iff (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hs : 3 ≤ s) (r : ℕ) (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (k : ℕ) (ρ : ℝ) (d : ℤ) :
    V38RestrictionProfiles.TwoThresholdProfile
      (V39RecursiveTable.matrix (V39EdgeSourceFront.edgeActivity g hg hs r hq) k)
      (laws g.vertices p q₁ q₂ s w Q k).1.toFiniteLaw (laws g.vertices p q₁ q₂ s w Q k).2.toFiniteLaw ρ d ↔
    V38RestrictionProfiles.TwoThresholdProfile
      (V39RecursiveTable.matrix (ownerActivity g hg hs r hq) k)
      (laws g.vertices p q₁ q₂ s w Q k).1.toFiniteLaw (laws g.vertices p q₁ q₂ s w Q k).2.toFiniteLaw ρ d := by
  rw [graph_activity]
  exact profile_map_iff _ _ _ _ _

theorem graph_sampledTable (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hs : 3 ≤ s) (r : ℕ) (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (k m : ℕ) (z) :
    V39RecursiveTable.sampledTable (V39EdgeSourceFront.edgeActivity g hg hs r hq) k m
      (sampleEquiv g.vertices p q₁ q₂ s w Q (graphPermutation g r hq) k m z) =
    V39RecursiveTable.sampledTable (ownerActivity g hg hs r hq) k m z := by
  rw [graph_activity]
  exact sampledTable_map _ _ _ _ _

/-- The physical and owner sampled tables have exactly the same law on
every event, with the literal current iid sample law on both sides. -/
theorem graph_table_event (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hs : 3 ≤ s) (r : ℕ) (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (k m : ℕ) (E : YaoMaterialization.SerializedTable m m → Prop) :
    (sampleLaw g.vertices p q₁ q₂ s w Q k m).toFiniteLaw.prob
      (fun z => E (V39RecursiveTable.sampledTable (ownerActivity g hg hs r hq) k m z)) =
    (sampleLaw g.vertices p q₁ q₂ s w Q k m).toFiniteLaw.prob
      (fun z => E (V39RecursiveTable.sampledTable (V39EdgeSourceFront.edgeActivity g hg hs r hq) k m z)) := by
  have h := sampleLaw_pushes g.vertices p q₁ q₂ s w Q (graphPermutation g r hq) k m
    (fun z => E (V39RecursiveTable.sampledTable (V39EdgeSourceFront.edgeActivity g hg hs r hq) k m z))
  simpa only [graph_sampledTable] using h

/-- The same transport preserves the literal encoded output and public
communication budget, for every sample including repeated labels. -/
theorem graph_outputWord (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hs : 3 ≤ s) (r : ℕ) (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (k m B : ℕ) (z) :
    V39RecursiveTable.outputWord (V39EdgeSourceFront.edgeActivity g hg hs r hq) k m B
      (sampleEquiv g.vertices p q₁ q₂ s w Q (graphPermutation g r hq) k m z) =
    V39RecursiveTable.outputWord (ownerActivity g hg hs r hq) k m B z := by
  unfold V39RecursiveTable.outputWord V39RecursiveTable.tableInstance
  rw [graph_sampledTable]

theorem graph_outputWord_event (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hs : 3 ≤ s) (r : ℕ) (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (k m B : ℕ) (E : List Bool → Prop) :
    (sampleLaw g.vertices p q₁ q₂ s w Q k m).toFiniteLaw.prob
      (fun z => E (V39RecursiveTable.outputWord (ownerActivity g hg hs r hq) k m B z)) =
    (sampleLaw g.vertices p q₁ q₂ s w Q k m).toFiniteLaw.prob
      (fun z => E (V39RecursiveTable.outputWord (V39EdgeSourceFront.edgeActivity g hg hs r hq) k m B z)) := by
  have h := sampleLaw_pushes g.vertices p q₁ q₂ s w Q (graphPermutation g r hq) k m
    (fun z => E (V39RecursiveTable.outputWord (V39EdgeSourceFront.edgeActivity g hg hs r hq) k m B z))
  simpa only [graph_outputWord] using h

end
end CurrentAdditive.V39SelectorTransport

#print axioms CurrentAdditive.V39SelectorTransport.graph_matrix
#print axioms CurrentAdditive.V39SelectorTransport.graph_profile_iff
#print axioms CurrentAdditive.V39SelectorTransport.graph_table_event
