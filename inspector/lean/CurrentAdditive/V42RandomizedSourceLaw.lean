import CurrentAdditive.V42RandomizedSourceData
import CurrentAdditive.V42PrintedGraphGap

namespace CurrentAdditive.V42RandomizedETHEndpoint
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite Unit4Shell.Asymptotics
open V42PublicSchedule V39ActualOutputMajority V39PermittedNumericalExtraction
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- Actual permitted estimator accuracy yields the stated decision event
on the exact new raw printer request. Source geometry, table gap, rounding,
midpoint code and independent classifier law are derived from their owners. -/
theorem permitted_source_law_all_large (A : PermittedEstimator)
    (cs T₀ : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1/8)
    (hA : GrowingSquareAccuracy A c T₀) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables → N₀ ≤ Φ.val.variables →
      ∀ ht : V42RuntimeSchedule.FullTests
        (V38Schedule.fullConstant (sourceGap D B) B.degreeBound
          (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length)
        (Nat.clog 2 (t10Graph D B Φ).vertices) (t10Graph D B Φ).edges.length
        (V38Schedule.sourceDeltaV (sourceGap D B) B.degreeBound
          (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length)
        (V38Schedule.sourceZeta (sourceGap D B)),
      (EncodedCNF.Satisfiable Φ.val →
        (99:ℝ)/100 ≤ (sourceLaw D B (extractedEstimator A) Φ).prob
          (fun z => sourceAccepts D B Φ ht (extractedEstimator A) z.1 z.2)) ∧
      (¬EncodedCNF.Satisfiable Φ.val →
        (sourceLaw D B (extractedEstimator A) Φ).prob
          (fun z => sourceAccepts D B Φ ht (extractedEstimator A) z.1 z.2) ≤ (3:ℝ)/100) := by
  obtain ⟨Nn,hNn,hnum⟩ := current_numeric_cutoff B.degreeBound (D.sizeExponent+2) T₀
    B.degreeBound_pos (extractedEstimator A).classifier c hc0 hc
  refine ⟨max Nn (max (V42SourceGeometry.originalCutoff D B cs)
    (B.degreeBound*V42FullCutoff.sourceCutoff (sourceGap D B) B.degreeBound)),
    hNn.trans (le_max_left _ _),?_⟩
  intro Φ hsp hN ht
  obtain ⟨facts,_,hsize⟩ := V42SourceGeometry.source_all_large D B cs Φ hsp
    ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  obtain ⟨hk,hT,_,hu,hgap,_⟩ := hnum Φ.val.variables ((le_max_left _ _).trans hN)
    (t10Graph D B Φ).vertices facts.vertices_pos facts.original_degree_bound hsize
  letI : NeZero (t10Graph D B Φ).vertices := ⟨facts.vertices_pos.ne'⟩
  let E := extractedEstimator A
  let L := Nat.clog 2 (t10Graph D B Φ).vertices
  let K := kOf Φ.val.variables
  let cc := V38Schedule.fullConstant (sourceGap D B) B.degreeBound
    (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length
  let δv := V38Schedule.sourceDeltaV (sourceGap D B) B.degreeBound
    (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length
  let ζ := V38Schedule.sourceZeta (sourceGap D B)
  let f := V42RawRequestPacket.matrix (t10Graph D B Φ) (t10Graph_valid D B Φ) K cc δv ζ ht
  let μ := RoundedDraw.bitBlocksLaw (V42RawSamplerJoin.precision (t10Graph D B Φ).vertices K)
    (V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices K)
  have haccurate := extracted_accuracy A c T₀ L K hA hT
  have hlarge : V42FullCutoff.sourceCutoff (sourceGap D B) B.degreeBound ≤
      (t10Graph D B Φ).vertices := facts.vertices_floor _
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hs := DeterministicETHSourceBridge.fixed_graph_source D B Φ
  constructor
  · intro hy
    obtain ⟨colour,proper⟩ := hs.2.2.2.2.2.1 hy
    have hproper : ∀ e, colour (LiteralEdgeEncoder.edge (t10Graph D B Φ)
        (t10Graph_valid D B Φ) e false) ≠ colour (LiteralEdgeEncoder.edge (t10Graph D B Φ)
        (t10Graph_valid D B Φ) e true) := by
      rw [V39SourceGeometry.physical_edge_eq]
      exact proper
    exact V42JointEstimatorLaw.yes_product μ E L K f _ hu hgap
      (fun bits => extractedEstimator_comparison A L K (f bits))
      (fun bits => haccurate (f bits))
      (fun bits => V42PrintedGraphGap.every_tape_yes (t10Graph D B Φ) (t10Graph_valid D B Φ)
        K cc δv ζ ht colour hproper bits)
  · intro hn
    have hgood := V42PrintedGraphGap.no_probability (t10Graph D B Φ) (t10Graph_valid D B Φ)
      K cc δv ζ ht B.degreeBound B.degreeBound_pos facts.degree (sourceGap D B)
      (source_gap_pos D B) facts.vertex_edge_bound facts.edge_degree_bound hlarge (by
        rw [V39SourceGeometry.physical_edge_eq]
        exact hs.2.2.2.2.2.2 hn)
    exact V42JointEstimatorLaw.no_product μ E L K f _ hu hgap
      (fun bits => extractedEstimator_comparison A L K (f bits))
      (fun bits => haccurate (f bits)) hgood

#print axioms permitted_source_law_all_large
end
end CurrentAdditive.V42RandomizedETHEndpoint
