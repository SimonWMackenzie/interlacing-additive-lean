import CurrentAdditive.V39ActualSquare
import CurrentAdditive.DeterministicETHGapNo
import CurrentAdditive.GraphCopyEncoded
import CurrentAdditive.V38SourcePaddingFinal

/-! Approved Dinur/BOT source → ORIGINAL-input-size graph copies → actual
public generated table. The supplied source interface already returns at
least as many edge occurrences as formula variables, so its prescribed
copy operation is exactly one copy. No source record is strengthened or
instantiated here. External theorem-record fidelity remains a separate boundary.
-/

namespace CurrentAdditive.V39CurrentSourceJoin

open Paper2
open Paper2.Unit4Shell.T10Finite
open Paper2.CurrentAdditive.GraphCopyPadding
open Paper2.CurrentAdditive.V38SourcePaddingFinal
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open CurrentAdditive.V39GeneratedConstruction
open Workspace.Types.CommComplexity

theorem copies_eq_one (N m : ℕ) (hm : 0 < m) (hNm : N ≤ m) : copies N m = 1 := by
  have hdiv : (N+m-1)/m < 2 := (Nat.div_lt_iff_lt_mul hm).2 (by omega)
  unfold copies
  omega

theorem encodedCopies_one (g : EncodedGraph.Graph) : encodedCopies g 1 = g := by
  cases g
  simp [encodedCopies, List.range_succ]

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- The threshold of the graph-copy stage is the original formula variable
count. In particular it is not the generated reduction's sufficient cutoff. -/
theorem original_size_copied_source (Φ : ValidFormula) :
    encodedCopies (t10Graph D B Φ)
      (copies Φ.val.variables (t10Graph D B Φ).edges.length) = t10Graph D B Φ := by
  have h := DeterministicETHSourceBridge.fixed_graph_source D B Φ
  rw [copies_eq_one Φ.val.variables _ h.1 h.2.1, encodedCopies_one]

theorem source_geometry (Φ : ValidFormula) :
    0 < (t10Graph D B Φ).vertices ∧
    (t10Graph D B Φ).vertices ≤ 2*(t10Graph D B Φ).edges.length ∧
    2*(t10Graph D B Φ).edges.length ≤ B.degreeBound*(t10Graph D B Φ).vertices := by
  have h := DeterministicETHSourceBridge.fixed_graph_source D B Φ
  have hbounds := source_edge_vertex_bounds
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound h.2.2.1 h.2.2.2.1
  exact ⟨t10_vertices_pos D B Φ, by simpa only [Fintype.card_fin] using hbounds⟩

def parameters : SourceConstants :=
  sourceConstants (sourceGap D B) B.degreeBound (source_gap_pos D B) B.degreeBound_pos

noncomputable def run (Φ : ValidFormula) (k : ℕ) : StoredMatrix :=
  publicGraphRun (parameters D B) (source_geometry D B Φ).1
    (source_geometry D B Φ).2.1 (source_geometry D B Φ).2.2
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) k

noncomputable def threshold (Φ : ValidFormula) (k : ℕ) : ℕ :=
  publicGraphThreshold (parameters D B) _ _ (source_geometry D B Φ).1
    (source_geometry D B Φ).2.1 (source_geometry D B Φ).2.2 k

noncomputable def word (Φ : ValidFormula) (k : ℕ) : List Bool := (run D B Φ k).squareWord

theorem word_target (Φ : ValidFormula) (k : ℕ) :
    Paper2.AModel.targetD (word D B Φ k) =
      some (Workspace.Types.CommComplexity.D (run D B Φ k).entry) :=
  StoredMatrix.squareWord_target _

/-- YES correctness is stated independently from the NO promise. The same
computed word and public threshold are used in both cases. -/
theorem run_yes (Φ : ValidFormula) (k : ℕ)
    (hyes : EncodedCNF.Satisfiable Φ.val) :
    Workspace.Types.CommComplexity.D (run D B Φ k).entry ≤ threshold D B Φ k := by
  obtain ⟨colour, proper⟩ :=
    (DeterministicETHSourceBridge.fixed_graph_source D B Φ).2.2.2.2.2.1 hyes
  exact publicGraphRun_yes (parameters D B) (source_geometry D B Φ).1
    (source_geometry D B Φ).2.1 (source_geometry D B Φ).2.2
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    k colour proper

/-- The NO source premise is derived only on unsatisfiable inputs; it is not
a global premise of run, word or their YES guarantee. -/
theorem source_no (Φ : ValidFormula) (hno : ¬ EncodedCNF.Satisfiable Φ.val) :
    DeterministicETHGapNo.GapNo (parameters D B).gamma
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) :=
  DeterministicETHGapNo.t10_no_gap D B Φ hno

/-- The already admitted physical copier is supplied its literal original N.
Its final output is exactly the graph consumed by run above. This does not
assert that source invocation, unary setup, parameter computation, or the
whole table printer has already been physically composed with this program. -/
theorem physical_copy_same_graph (Φ : ValidFormula) :
    ∃ t ≤ Paper2.CurrentAdditive.GraphCopyEncoded.totalBound
        (t10Graph D B Φ) Φ.val.variables,
      Paper2.CurrentAdditive.GraphCopyEncoded.run t
        (Paper2.CurrentAdditive.GraphCopyEncoded.start
          (EncodedGraph.encode (t10Graph D B Φ)) Φ.val.variables) =
            Paper2.CurrentAdditive.GraphCopyEncoded.finalHost
              (t10Graph D B Φ) Φ.val.variables ∧
      (Paper2.CurrentAdditive.GraphCopyEncoded.finalHost
        (t10Graph D B Φ) Φ.val.variables).stk
          Paper2.CurrentAdditive.GraphCopyEncoded.outputStack =
            EncodedGraph.encode (t10Graph D B Φ) := by
  obtain ⟨t, ht, hr⟩ := Paper2.CurrentAdditive.GraphCopyEncoded.encoded_graph_copy_run
    (t10Graph D B Φ) (t10Graph_valid D B Φ) Φ.val.variables
    (DeterministicETHSourceBridge.fixed_graph_source D B Φ).1
  refine ⟨t, ht, hr, ?_⟩
  rw [Paper2.CurrentAdditive.GraphCopyEncoded.final_output, original_size_copied_source D B Φ]

end CurrentAdditive.V39CurrentSourceJoin

#print axioms CurrentAdditive.V39CurrentSourceJoin.original_size_copied_source
#print axioms CurrentAdditive.V39CurrentSourceJoin.run_yes
#print axioms CurrentAdditive.V39CurrentSourceJoin.source_no
#print axioms CurrentAdditive.V39CurrentSourceJoin.physical_copy_same_graph
