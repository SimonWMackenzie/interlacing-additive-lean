import CurrentAdditive.V39CurrentSourceJoin
import CurrentAdditive.V39FloorOutput

/-! The approved source composed with the deterministic ETH search floor.
All finite constructor/YES/printed-size results concern the same actual word.
This supplies neither the still-open generated NO successor nor its physical
whole-round bit clock, so it is not an ETH-hardness completion certificate.
-/

namespace CurrentAdditive.V39CurrentSourceJoin

open Paper2 Paper2.Unit4Shell.T10Finite V38Schedule
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open CurrentAdditive.V39GeneratedConstruction

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

noncomputable def ethRun (Φ : ValidFormula) (k : ℕ) : StoredMatrix :=
  publicGraphRunFrom (parameters D B) Φ.val.variables (source_geometry D B Φ).1
    (source_geometry D B Φ).2.1 (source_geometry D B Φ).2.2
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) k

noncomputable def ethThreshold (Φ : ValidFormula) (k : ℕ) : ℕ :=
  publicGraphThresholdFrom (parameters D B) Φ.val.variables _ _ (source_geometry D B Φ).1
    (source_geometry D B Φ).2.1 (source_geometry D B Φ).2.2 k

noncomputable def ethWord (Φ : ValidFormula) (k : ℕ) : List Bool := (ethRun D B Φ k).squareWord

theorem ethWord_target (Φ : ValidFormula) (k : ℕ) :
    Paper2.AModel.targetD (ethWord D B Φ k) =
      some (Workspace.Types.CommComplexity.D (ethRun D B Φ k).entry) :=
  StoredMatrix.squareWord_target _

theorem ethRun_yes (Φ : ValidFormula) (k : ℕ)
    (hyes : EncodedCNF.Satisfiable Φ.val) :
    Workspace.Types.CommComplexity.D (ethRun D B Φ k).entry ≤ ethThreshold D B Φ k := by
  obtain ⟨colour, proper⟩ :=
    (DeterministicETHSourceBridge.fixed_graph_source D B Φ).2.2.2.2.2.1 hyes
  exact publicGraphRunFrom_yes (parameters D B) Φ.val.variables
    (source_geometry D B Φ).1 (source_geometry D B Φ).2.1 (source_geometry D B Φ).2.2
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) k colour proper

theorem ethWord_size (Φ : ValidFormula) (k : ℕ) :
    let L := publicLogFrom (parameters D B) Φ.val.variables
      (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length
      (source_geometry D B Φ).1 (source_geometry D B Φ).2.1 (source_geometry D B Φ).2.2
    Φ.val.variables^2 ≤
      (Paper2.SquarePadding.side (ethRun D B Φ k).rows (ethRun D B Φ k).cols)^2 ∧
      (ethWord D B Φ k).length ≤ (generatedN L)^(1040*supportAmplification^k) := by
  have h := publicGraphRunFrom_size_bounds (parameters D B) Φ.val.variables
    (source_geometry D B Φ).1 (source_geometry D B Φ).2.1 (source_geometry D B Φ).2.2
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) k
  exact ⟨h.1, h.2.2⟩

end CurrentAdditive.V39CurrentSourceJoin

#print axioms CurrentAdditive.V39CurrentSourceJoin.ethRun_yes
#print axioms CurrentAdditive.V39CurrentSourceJoin.ethWord_size
