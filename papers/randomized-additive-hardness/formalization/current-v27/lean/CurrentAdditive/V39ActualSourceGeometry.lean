import CurrentAdditive.V39CurrentSourceJoin
import CurrentAdditive.V39FullCutoff
import CurrentAdditive.EdgeEncoder

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace CurrentAdditive.V39SourceGeometry
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- The executable edge decoder reads the same actual source endpoints. -/
theorem physical_edge_eq (Φ : ValidFormula) :
    LiteralEdgeEncoder.edge (t10Graph D B Φ) (t10Graph_valid D B Φ) =
      CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ) := by
  funext e b
  apply Fin.ext
  cases b <;> simp [LiteralEdgeEncoder.edge,CanonicalEdgeTape.graphEdge]

/-- Source facts only: this record supplies no sampler, run, law or clock. -/
structure Facts (Φ : ValidFormula) : Prop where
  valid : (t10Graph D B Φ).Valid
  vertices_pos : 0 < (t10Graph D B Φ).vertices
  edges_pos : 0 < (t10Graph D B Φ).edges.length
  original_floor : Φ.val.variables ≤ (t10Graph D B Φ).edges.length
  incident : ∀ v, ∃ e b, LiteralEdgeEncoder.edge (t10Graph D B Φ) (t10Graph_valid D B Φ) e b = v
  degree : ∀ v, SourceItems.degree
    (LiteralEdgeEncoder.edge (t10Graph D B Φ) (t10Graph_valid D B Φ)) v ≤ B.degreeBound
  loopless : ∀ e, LiteralEdgeEncoder.edge (t10Graph D B Φ) (t10Graph_valid D B Φ) e false ≠
    LiteralEdgeEncoder.edge (t10Graph D B Φ) (t10Graph_valid D B Φ) e true
  vertex_edge_bound : (t10Graph D B Φ).vertices ≤ 2*(t10Graph D B Φ).edges.length
  edge_degree_bound : 2*(t10Graph D B Φ).edges.length ≤ B.degreeBound*(t10Graph D B Φ).vertices
  original_degree_bound : Φ.val.variables ≤ B.degreeBound*(t10Graph D B Φ).vertices
  vertices_floor : ∀ a : ℕ, B.degreeBound*a ≤ Φ.val.variables → a ≤ (t10Graph D B Φ).vertices
  full_tests : B.degreeBound*V39FullCutoff.sourceCutoff (sourceGap D B) B.degreeBound ≤
    Φ.val.variables → V38Schedule.FullPublicTests (sourceGap D B) B.degreeBound
      (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length
      (Nat.clog 2 (t10Graph D B Φ).vertices)
  sparse_size : ∀ cs : ℕ, Φ.val.clauses.length ≤ cs*Φ.val.variables →
    2^(2^(D.sizeExponent+1)*Unit4Shell.T10Size.t45C D B cs) ≤ Φ.val.variables →
    (t10Graph D B Φ).vertices ≤ Φ.val.variables*(Nat.clog 2 (Φ.val.variables+2))^(D.sizeExponent+2)

/-- Exact source geometry for the actual graph emitted by the approved
Dinur/Boolean/BOT compiler, with its original-variable source-copy floor. -/
theorem source_only (Φ : ValidFormula) : Facts D B Φ := by
  have hsource := DeterministicETHSourceBridge.fixed_graph_source D B Φ
  have hgeom := V39CurrentSourceJoin.source_geometry D B Φ
  have hfloor : ∀ a : ℕ, B.degreeBound*a ≤ Φ.val.variables → a ≤ (t10Graph D B Φ).vertices := by
    intro a ha
    have hprod : B.degreeBound*a ≤ B.degreeBound*(t10Graph D B Φ).vertices := by
      have := hsource.2.1
      have := hgeom.2.2
      omega
    by_contra hc
    have hlt : (t10Graph D B Φ).vertices < a := Nat.lt_of_not_ge hc
    have := Nat.mul_lt_mul_of_pos_left hlt B.degreeBound_pos
    omega
  refine ⟨t10Graph_valid D B Φ,hgeom.1,hsource.1,hsource.2.1,?_,?_,?_,hgeom.2.1,hgeom.2.2,?_,hfloor,?_,?_⟩
  · rw [physical_edge_eq]; exact hsource.2.2.1
  · rw [physical_edge_eq]; exact hsource.2.2.2.1
  · rw [physical_edge_eq]; exact hsource.2.2.2.2.1
  · have := hsource.2.1; have := hgeom.2.2; omega
  · intro hN
    exact V39FullCutoff.fullPublicTests_all_large _ _ _ _ (source_gap_pos D B)
      B.degreeBound_pos hgeom.1 hgeom.2.1 hgeom.2.2 (hfloor _ hN)
  · intro cs
    exact Unit4Shell.T10Size.t45_shell_form D B cs Φ

/-- One fixed original-variable threshold covers both actual public tests
and the source's quasi-linear vertex bound. -/
def originalCutoff (cs : ℕ) : ℕ :=
  max (B.degreeBound*V39FullCutoff.sourceCutoff (sourceGap D B) B.degreeBound)
    (2^(2^(D.sizeExponent+1)*Unit4Shell.T10Size.t45C D B cs))

theorem originalCutoff_pos (cs : ℕ) : 0 < originalCutoff D B cs := by
  unfold originalCutoff
  exact lt_of_lt_of_le (Nat.two_pow_pos _) (le_max_right _ _)

theorem source_all_large (cs : ℕ) (Φ : ValidFormula)
    (hsp : Φ.val.clauses.length ≤ cs*Φ.val.variables)
    (hN : originalCutoff D B cs ≤ Φ.val.variables) :
    Facts D B Φ ∧
    V38Schedule.FullPublicTests (sourceGap D B) B.degreeBound
      (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length
      (Nat.clog 2 (t10Graph D B Φ).vertices) ∧
    (t10Graph D B Φ).vertices ≤ Φ.val.variables*(Nat.clog 2 (Φ.val.variables+2))^(D.sizeExponent+2) := by
  have h := source_only D B Φ
  exact ⟨h,h.full_tests ((le_max_left _ _).trans hN),
    h.sparse_size cs hsp ((le_max_right _ _).trans hN)⟩

end
end CurrentAdditive.V39SourceGeometry
#print axioms CurrentAdditive.V39SourceGeometry.source_only
#print axioms CurrentAdditive.V39SourceGeometry.source_all_large
