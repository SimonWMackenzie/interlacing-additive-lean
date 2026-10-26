import CurrentAdditive.V39ActualGraphNo
import CurrentAdditive.V39SourceFloorJoin

/-! The approved source gap applied to the actual stored constructions.
The YES and NO conclusions concern the same square words and public thresholds.
This finite correctness join makes no assertion about the constructor clock. -/

namespace CurrentAdditive.V39CurrentSourceJoin

open Paper2 Paper2.Unit4Shell.T10Finite
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open CurrentAdditive.V39GeneratedConstruction

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

theorem run_no (Φ : ValidFormula) (k : ℕ)
    (hno : ¬ EncodedCNF.Satisfiable Φ.val) :
    Workspace.Types.CommComplexity.D (run D B Φ k).entry = threshold D B Φ k + k := by
  have h := DeterministicETHSourceBridge.fixed_graph_source D B Φ
  exact (publicGraphRun_no (parameters D B) (source_geometry D B Φ).1
    (source_geometry D B Φ).2.1 (source_geometry D B Φ).2.2
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    h.2.2.2.2.1 h.2.2.2.1 (source_no D B Φ hno) k).1

theorem ethRun_no (Φ : ValidFormula) (k : ℕ)
    (hno : ¬ EncodedCNF.Satisfiable Φ.val) :
    Workspace.Types.CommComplexity.D (ethRun D B Φ k).entry =
      ethThreshold D B Φ k + k := by
  have h := DeterministicETHSourceBridge.fixed_graph_source D B Φ
  exact (publicGraphRunFrom_no (parameters D B) Φ.val.variables
    (source_geometry D B Φ).1 (source_geometry D B Φ).2.1
    (source_geometry D B Φ).2.2
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    h.2.2.2.2.1 h.2.2.2.1 (source_no D B Φ hno) k).1

theorem word_no (Φ : ValidFormula) (k : ℕ)
    (hno : ¬ EncodedCNF.Satisfiable Φ.val) :
    Paper2.AModel.targetD (word D B Φ k) = some (threshold D B Φ k + k) := by
  rw [word_target, run_no D B Φ k hno]

theorem ethWord_no (Φ : ValidFormula) (k : ℕ)
    (hno : ¬ EncodedCNF.Satisfiable Φ.val) :
    Paper2.AModel.targetD (ethWord D B Φ k) = some (ethThreshold D B Φ k + k) := by
  rw [ethWord_target, ethRun_no D B Φ k hno]

end CurrentAdditive.V39CurrentSourceJoin

#print axioms CurrentAdditive.V39CurrentSourceJoin.run_no
#print axioms CurrentAdditive.V39CurrentSourceJoin.ethRun_no
#print axioms CurrentAdditive.V39CurrentSourceJoin.word_no
#print axioms CurrentAdditive.V39CurrentSourceJoin.ethWord_no
