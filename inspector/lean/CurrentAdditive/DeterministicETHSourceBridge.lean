import Paper2.CNFGraphMachine
import Paper2.A4T10Size

/-! The inherited physical sparse-formula-to-graph machine, specialized
to the exact graph used by the deterministic generated successor. The cited
Dinur and BOT records remain the paper's explicit external inputs. -/

namespace CurrentAdditive.DeterministicETHSourceBridge

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2
open Paper2.Unit4Shell.T10Finite

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- The fixed all-input graph machine is polynomial-time. Its cutoff is
chosen once, not separately for each sparse input formula. -/
theorem fixed_graph_compiler (cutoff : ℕ) (hcutoff : 1 ≤ cutoff) :
    BitMachine.Polytime (Paper2.CNFGraphGuard.graphWord D B hcutoff) :=
  Paper2.CNFGraphGuard.graphWord_polytime D B hcutoff

/-- Above the fixed small-input cutoff, that machine prints the literal
T10 graph of the input formula. -/
theorem fixed_graph_word_eq (cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (Φ : ValidFormula) (hlarge : cutoff ≤ Φ.val.variables) :
    Paper2.CNFGraphGuard.graphWord D B hcutoff (EncodedCNF.encode Φ.val) =
      EncodedGraph.encode (t10Graph D B Φ) := by
  have hd : EncodedCNF.decode (EncodedCNF.encode Φ.val) = some Φ.val :=
    EncodedCNF.decode_encode Φ.val Φ.property
  have hr := AFront.T10.routed_large hcutoff hd hlarge
  have hΦ : AFront.T10.routed hcutoff (EncodedCNF.encode Φ.val) = Φ :=
    Subtype.ext hr
  unfold Paper2.CNFGraphGuard.graphWord
  rw [hΦ]

/-- One fixed physical source compiler prints the very graph whose
vertices, edges and colour gap enter the deterministic schedule.  Its
machine and polynomial constants are fixed before the formula is known. -/
theorem fixed_graph_machine (cutoff : ℕ) (hcutoff : 1 ≤ cutoff) :
    ∃ (M : BitMachine.Machine) (C E : ℕ),
      ∀ (Φ : ValidFormula), cutoff ≤ Φ.val.variables →
        M.OutputsWithin (EncodedCNF.encode Φ.val)
          (EncodedGraph.encode (t10Graph D B Φ))
          (C * ((EncodedCNF.encode Φ.val).length + 1)^E) := by
  obtain ⟨M, C, E, hM⟩ := fixed_graph_compiler D B cutoff hcutoff
  refine ⟨M, C, E, ?_⟩
  intro Φ hlarge
  simpa only [fixed_graph_word_eq D B cutoff hcutoff Φ hlarge] using
    hM (EncodedCNF.encode Φ.val)

/-- The exact sparse source graph meets the deterministic Appendix I
degree and colour-gap premises. These are read from the same T10 object
that the physical graph machine prints. -/
theorem fixed_graph_source (Φ : ValidFormula) :
    0 < (t10Graph D B Φ).edges.length ∧
    Φ.val.variables ≤ (t10Graph D B Φ).edges.length ∧
    (∀ v, ∃ e b, CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
      (t10Graph_valid D B Φ) e b = v) ∧
    (∀ v, SourceItems.degree
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
        (t10Graph_valid D B Φ)) v ≤ B.degreeBound) ∧
    (∀ e, CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
      (t10Graph_valid D B Φ) e false ≠
      CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
        (t10Graph_valid D B Φ) e true) ∧
    (EncodedCNF.Satisfiable Φ.val → FiniteFallbackOutput.ThreeColourable
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))) ∧
    (¬ EncodedCNF.Satisfiable Φ.val →
      ∀ colour : Fin (t10Graph D B Φ).vertices → Fin 3,
        ((sourceGap D B : ℚ) : ℝ) * (t10Graph D B Φ).edges.length ≤
          ((Finset.univ.filter (fun e =>
            colour (CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
              (t10Graph_valid D B Φ) e false) =
            colour (CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
              (t10Graph_valid D B Φ) e true))).card : ℝ)) :=
  t10_source D B Φ

#print axioms fixed_graph_compiler
#print axioms fixed_graph_word_eq
#print axioms fixed_graph_machine
#print axioms fixed_graph_source

end CurrentAdditive.DeterministicETHSourceBridge
