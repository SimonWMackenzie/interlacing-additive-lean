import CurrentAdditive.V42ActualSource
import CurrentAdditive.V42GeneratedIteration

namespace CurrentAdditive.V42ActualSource
noncomputable section
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V42Schedule V39GeneratedConstruction
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

theorem run_no (Φ : ValidFormula) (K : ℕ) (hno : ¬ EncodedCNF.Satisfiable Φ.val) :
    Workspace.Types.CommComplexity.D (run D B Φ K).entry = threshold D B Φ K+K := by
  have hg := DeterministicETHSourceBridge.fixed_graph_source D B Φ
  have hgeom := V39CurrentSourceJoin.source_geometry D B Φ
  have hk : commonCutoff (V38Schedule.sourceDeltaV (sourceGap D B) B.degreeBound
      (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length)
      (V38Schedule.sourceZeta (sourceGap D B)) B.degreeBound ≤ selected D B Φ := by
    apply fixedPromiseCutoff_graph (sourceGap D B) B.degreeBound _ _ _
      (source_gap_pos D B) B.degreeBound_pos hgeom.1 hgeom.2.1
    exact (V42PublicCutoff.generatedExponent_spec (t10Graph D B Φ).vertices (k0 D B)).1
  have h := V42GeneratedNo.graphRun_no (sourceGap D B) B.degreeBound
    (source_gap_pos D B) B.degreeBound_pos hgeom.1 hg.1 hk (selected_two D B Φ)
    (V42GraphRuntime.selected_width B.degreeBound (k0 D B) (t10Graph D B Φ)
      hgeom.2.2 (k0_degree D B))
    (LiteralEdgeEncoder.edge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    (by simpa only [LiteralEdgeScanValue.edge_eq_canonical] using hg.2.2.2.2.1)
    (by simpa only [LiteralEdgeScanValue.edge_eq_canonical] using hg.2.2.2.1)
    (by simpa only [LiteralEdgeScanValue.edge_eq_canonical] using hg.2.2.2.2.2.2 hno) K
  have he : LookupSeed.exponent (4*selected D B Φ)+1+K*(40*selected D B Φ+1)=
      threshold D B Φ K+K := by unfold threshold; ring
  exact h.1.trans he

#print axioms run_no
end
end CurrentAdditive.V42ActualSource
