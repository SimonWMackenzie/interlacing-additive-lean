import CurrentV43.TimeTradeoff.SourceBounds
import CurrentAdditive.V42PrintedGraphGap

/-! The finite SAT correctness join for v43 `thm:time-tradeoff`, at an
arbitrary supplied gap K. The construction events here are the actual
same-table events of the checked v42 source theorem, not supplied success
certificates. Physical caller and runtime assembly remain separate. -/
namespace CurrentV43.TimeTradeoff
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39ActualOutputMajority V39PermittedNumericalExtraction
open V39PermittedDeterministicExtraction Workspace.Types.CommComplexity
set_option maxHeartbeats 2000000
set_option maxRecDepth 65536

variable (Src : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Src))

def SourceTests (Φ : ValidFormula) : Prop :=
  V42RuntimeSchedule.FullTests
    (V38Schedule.fullConstant (sourceGap Src Bsrc) Bsrc.degreeBound
      (t10Graph Src Bsrc Φ).vertices (t10Graph Src Bsrc Φ).edges.length)
    (Nat.clog 2 (t10Graph Src Bsrc Φ).vertices) (t10Graph Src Bsrc Φ).edges.length
    (V38Schedule.sourceDeltaV (sourceGap Src Bsrc) Bsrc.degreeBound
      (t10Graph Src Bsrc Φ).vertices (t10Graph Src Bsrc Φ).edges.length)
    (V38Schedule.sourceZeta (sourceGap Src Bsrc))

def sampledSource (Φ : ValidFormula) (K : ℕ) (ht : SourceTests Src Bsrc Φ)
    (bits : V42PrintedCompression.Bits (t10Graph Src Bsrc Φ) K) :
    V42JointEstimatorLaw.Table (Nat.clog 2 (t10Graph Src Bsrc Φ).vertices) K := by
  letI : NeZero (t10Graph Src Bsrc Φ).vertices:=⟨(t10_vertices_pos Src Bsrc Φ).ne'⟩
  exact V42RawRequestPacket.matrix (t10Graph Src Bsrc Φ) (t10Graph_valid Src Bsrc Φ) K
    (V38Schedule.fullConstant (sourceGap Src Bsrc) Bsrc.degreeBound
      (t10Graph Src Bsrc Φ).vertices (t10Graph Src Bsrc Φ).edges.length)
    (V38Schedule.sourceDeltaV (sourceGap Src Bsrc) Bsrc.degreeBound
      (t10Graph Src Bsrc Φ).vertices (t10Graph Src Bsrc Φ).edges.length)
    (V38Schedule.sourceZeta (sourceGap Src Bsrc)) ht bits

theorem sampledSource_yes (Φ : ValidFormula) (K : ℕ) (ht : SourceTests Src Bsrc Φ)
    (hy : EncodedCNF.Satisfiable Φ.val)
    (bits : V42PrintedCompression.Bits (t10Graph Src Bsrc Φ) K) :
    D (sampledSource Src Bsrc Φ K ht bits) ≤
      V42PublicSchedule.B (Nat.clog 2 (t10Graph Src Bsrc Φ).vertices) K := by
  letI : NeZero (t10Graph Src Bsrc Φ).vertices:=⟨(t10_vertices_pos Src Bsrc Φ).ne'⟩
  obtain ⟨colour,proper⟩ :=
    (DeterministicETHSourceBridge.fixed_graph_source Src Bsrc Φ).2.2.2.2.2.1 hy
  exact V42PrintedGraphGap.every_tape_yes (t10Graph Src Bsrc Φ) (t10Graph_valid Src Bsrc Φ) K
    _ _ _ ht colour (by simpa only [LiteralEdgeScanValue.edge_eq_canonical] using proper) bits

theorem sampledSource_no (Φ : ValidFormula) (K : ℕ) (ht : SourceTests Src Bsrc Φ)
    (hlarge : V42FullCutoff.sourceCutoff (sourceGap Src Bsrc) Bsrc.degreeBound ≤
      (t10Graph Src Bsrc Φ).vertices)
    (hn : ¬EncodedCNF.Satisfiable Φ.val) :
    (49:ℝ)/50 ≤ (V42PrintedCompression.bitLaw (t10Graph Src Bsrc Φ) K).prob
      (fun bits => D (sampledSource Src Bsrc Φ K ht bits)=
        V42PublicSchedule.B (Nat.clog 2 (t10Graph Src Bsrc Φ).vertices) K+K) := by
  letI : NeZero (t10Graph Src Bsrc Φ).vertices:=⟨(t10_vertices_pos Src Bsrc Φ).ne'⟩
  have facts:=V39SourceGeometry.source_only Src Bsrc Φ
  have hgap:=(DeterministicETHSourceBridge.fixed_graph_source Src Bsrc Φ).2.2.2.2.2.2 hn
  have h:=V42PrintedGraphGap.no_probability (t10Graph Src Bsrc Φ) (t10Graph_valid Src Bsrc Φ) K
    _ _ _ ht Bsrc.degreeBound Bsrc.degreeBound_pos facts.degree (sourceGap Src Bsrc)
    (source_gap_pos Src Bsrc) facts.vertex_edge_bound facts.edge_degree_bound hlarge
    (by simpa only [LiteralEdgeScanValue.edge_eq_canonical] using hgap)
  simpa only [V42RuntimeSchedule.H,V42PublicSchedule.H] using h

/-- Finite arbitrary-K SAT correctness for the randomized construction and
randomized estimator. The sole construction-size assumptions are its actual
upper/lower table bounds; the success probability is proved from the source. -/
theorem randomized_source_correctness
    (A : PermittedEstimator) (a : ℕ → ℝ) (ha : Monotone a)
    (T₀ S K : ℕ) (hA : RandomizedSquareAccuracy A a T₀)
    (Φ : ValidFormula) (ht : SourceTests Src Bsrc Φ) (hu : 0 ≤ a S)
    (hlarge : V42FullCutoff.sourceCutoff (sourceGap Src Bsrc) Bsrc.degreeBound ≤
      (t10Graph Src Bsrc Φ).vertices)
    (hT : T₀ ≤ V42PublicSchedule.sampleEntries (Nat.clog 2 (t10Graph Src Bsrc Φ).vertices) K)
    (hS : V42PublicSchedule.sampleEntries (Nat.clog 2 (t10Graph Src Bsrc Φ).vertices) K ≤ S)
    (hgap : 2*a S < (K:ℝ)) :
    let L:=Nat.clog 2 (t10Graph Src Bsrc Φ).vertices
    let μ:=V42PrintedCompression.bitLaw (t10Graph Src Bsrc Φ) K
    let law:=V42JointEstimatorLaw.independentLaw μ (randomEstimator A) L K
    let accepts:=fun z=>V42JointEstimatorLaw.accepts (randomEstimator A) L K
      (sampledSource Src Bsrc Φ K ht z.1) z.2
    (EncodedCNF.Satisfiable Φ.val → (99:ℝ)/100 ≤ law.prob accepts) ∧
    (¬EncodedCNF.Satisfiable Φ.val → law.prob accepts ≤ (3:ℝ)/100) := by
  dsimp only
  have h:=randomized_estimator_randomized_construction A a ha T₀ S
    (Nat.clog 2 (t10Graph Src Bsrc Φ).vertices) K hA hu hT hS hgap
    (V42PrintedCompression.bitLaw (t10Graph Src Bsrc Φ) K) (sampledSource Src Bsrc Φ K ht)
  exact ⟨fun hy=>h.1 (sampledSource_yes Src Bsrc Φ K ht hy),
    fun hn=>h.2 (sampledSource_no Src Bsrc Φ K ht hlarge hn)⟩

/-- Replacing the estimator by a deterministic one keeps every YES run
correct and leaves only the construction's 1/50 NO failure. -/
theorem deterministic_estimator_sampled_source_correctness
    (A : PermittedDeterministicEstimator) (a : ℕ → ℝ) (ha : Monotone a)
    (T₀ S K : ℕ) (hA : DeterministicSquareAccuracy A a T₀)
    (Φ : ValidFormula) (ht : SourceTests Src Bsrc Φ)
    (hlarge : V42FullCutoff.sourceCutoff (sourceGap Src Bsrc) Bsrc.degreeBound ≤
      (t10Graph Src Bsrc Φ).vertices)
    (hT : T₀ ≤ V42PublicSchedule.sampleEntries (Nat.clog 2 (t10Graph Src Bsrc Φ).vertices) K)
    (hS : V42PublicSchedule.sampleEntries (Nat.clog 2 (t10Graph Src Bsrc Φ).vertices) K ≤ S)
    (hgap : 2*a S < (K:ℝ)) :
    let L:=Nat.clog 2 (t10Graph Src Bsrc Φ).vertices
    let μ:=V42PrintedCompression.bitLaw (t10Graph Src Bsrc Φ) K
    let result:=fun bits=>(deterministicEstimator A).run
      (V42JointEstimatorLaw.request L K (sampledSource Src Bsrc Φ K ht bits))
    (EncodedCNF.Satisfiable Φ.val → ∀ bits,result bits=[true]) ∧
    (¬EncodedCNF.Satisfiable Φ.val → (49:ℝ)/50 ≤ μ.prob (fun bits=>result bits=[false])) := by
  dsimp only
  have h:=deterministic_estimator_randomized_construction A a ha T₀ S
    (Nat.clog 2 (t10Graph Src Bsrc Φ).vertices) K hA hT hS hgap
    (V42PrintedCompression.bitLaw (t10Graph Src Bsrc Φ) K) (sampledSource Src Bsrc Φ K ht)
  exact ⟨fun hy=>h.1 (sampledSource_yes Src Bsrc Φ K ht hy),
    fun hn=>h.2 (sampledSource_no Src Bsrc Φ K ht hlarge hn)⟩

#print axioms sampledSource_yes
#print axioms sampledSource_no
#print axioms randomized_source_correctness
#print axioms deterministic_estimator_sampled_source_correctness
end
end CurrentV43.TimeTradeoff
