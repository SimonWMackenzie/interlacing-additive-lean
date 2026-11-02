import Paper2.AFrontT10

/-!
Paper A, lock v12 `appendices/C-parameters.tex:204-206`, source T10.
This is the semantic all-input graph guard. The physical CNF router is the admitted
`AFront.Route.frontRoute`; this file does not claim a graph-word Polytime map or a
total graph-language decider.
-/

namespace Paper2.CNFGraphGuard

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite
open AFront.T10

/-- The exact three-colourability language, distinct from `EncodedGraph.Language`,
whose colouring carrier has four colours. -/
def GraphThreeLanguage : Set (List Bool) :=
  {z | ∃ g, ∃ hg : g.Valid, EncodedGraph.decode z = some g ∧
    FiniteFallbackOutput.ThreeColourable (CanonicalEdgeTape.graphEdge g hg)}

theorem encoded_graph_mem_iff (g : EncodedGraph.Graph) (hg : g.Valid) :
    EncodedGraph.encode g ∈ GraphThreeLanguage ↔
      FiniteFallbackOutput.ThreeColourable (CanonicalEdgeTape.graphEdge g hg) := by
  constructor
  · rintro ⟨g', hg', hd, hc⟩
    rw [EncodedGraph.decode_encode g hg] at hd
    cases Option.some.inj hd
    exact hc
  · intro hc
    exact ⟨g, hg, EncodedGraph.decode_encode g hg, hc⟩

theorem source_three_iff (D : DinurReduction)
    (B : BOTReduction (booleanOccurrence D)) (Φ : ValidFormula) :
    FiniteFallbackOutput.ThreeColourable
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) ↔
      EncodedCNF.Satisfiable Φ.val := by
  have hs := t10_source D B Φ
  constructor
  · intro hc
    by_contra hno
    obtain ⟨colour, hproper⟩ := hc
    have hgap := hs.2.2.2.2.2.2 hno colour
    have hempty : Finset.univ.filter (fun e =>
        colour (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ) e false) =
          colour (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ) e true)) =
          (∅ : Finset (Fin (t10Graph D B Φ).edges.length)) := by
      ext e
      simp [hproper e]
    rw [hempty] at hgap
    have hγ : (0 : ℝ) < ((sourceGap D B : ℚ) : ℝ) := by
      exact_mod_cast source_gap_pos D B
    have hm : (0 : ℝ) < (t10Graph D B Φ).edges.length := by
      exact_mod_cast hs.1
    have hp := mul_pos hγ hm
    simp only [Finset.card_empty, Nat.cast_zero] at hgap
    linarith
  · exact hs.2.2.2.2.2.1

/-- Every raw CNF word, including malformed words and small formulas, is routed by
the admitted all-input front to a valid graph. Its exact three-colourability is
equivalent to membership in the chosen CNF language. -/
theorem routed_graph_mem_iff (D : DinurReduction)
    (B : BOTReduction (booleanOccurrence D)) {N : ℕ} (hN : 1 ≤ N)
    (w : List Bool) :
    EncodedGraph.encode (t10Graph D B (routed hN w)) ∈ GraphThreeLanguage ↔
      w ∈ EncodedCNF.Language := by
  rw [encoded_graph_mem_iff _ (t10Graph_valid D B (routed hN w)),
    source_three_iff D B (routed hN w)]
  exact AFront.Route.routedFormula_sat_iff hN w

#print axioms encoded_graph_mem_iff
#print axioms source_three_iff
#print axioms routed_graph_mem_iff

end Paper2.CNFGraphGuard
