import CurrentAdditive.V39ActualSourceGeometry
import CurrentAdditive.V42RuntimeSchedule

namespace CurrentAdditive.V42SourceGeometry
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite
set_option maxHeartbeats 1000000

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def originalCutoff (cs : ℕ) : ℕ :=
  max (V39SourceGeometry.originalCutoff D B cs)
    (B.degreeBound*V42RuntimeSchedule.sourceCutoff (sourceGap D B) B.degreeBound)

theorem originalCutoff_pos (cs : ℕ) : 0 < originalCutoff D B cs :=
  (V39SourceGeometry.originalCutoff_pos D B cs).trans_le (le_max_left _ _)

theorem source_all_large (cs : ℕ) (Φ : ValidFormula)
    (hsp : Φ.val.clauses.length ≤ cs*Φ.val.variables)
    (hN : originalCutoff D B cs ≤ Φ.val.variables) :
    V39SourceGeometry.Facts D B Φ ∧
    V42RuntimeSchedule.FullTests
      (V38Schedule.fullConstant (sourceGap D B) B.degreeBound
        (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length)
      (Nat.clog 2 (t10Graph D B Φ).vertices) (t10Graph D B Φ).edges.length
      (V38Schedule.sourceDeltaV (sourceGap D B) B.degreeBound
        (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length)
      (V38Schedule.sourceZeta (sourceGap D B)) ∧
    (t10Graph D B Φ).vertices ≤ Φ.val.variables*(Nat.clog 2 (Φ.val.variables+2))^(D.sizeExponent+2) := by
  obtain ⟨facts,_,hsize⟩ := V39SourceGeometry.source_all_large D B cs Φ hsp
    ((le_max_left _ _).trans hN)
  refine ⟨facts,?_,hsize⟩
  exact V42RuntimeSchedule.tests_all_large (sourceGap D B) B.degreeBound _ _
    (source_gap_pos D B) B.degreeBound_pos facts.vertices_pos
    facts.vertex_edge_bound facts.edge_degree_bound
    (facts.vertices_floor _ ((le_max_right _ _).trans hN))

#print axioms source_all_large
end
end CurrentAdditive.V42SourceGeometry
