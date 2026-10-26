import Paper2.A4T24Actual
import Paper2.A4LogBounds

/-!
# Unit 4 (Paper A), A4-S7: `T24_actual` with the proved `kOf` cutoff

Owner lane `owner:a-unit4-shell-4` (private, 26 September 2026).

`T24_actual_cut` has EXACTLY the statement of `T24Actual.T24_actual` (frozen R3 object, owner-3);
its proof is the owner-3 proof text with two changes only: the cutoff
`max N₀ (max 2 ⌈(2 : ℝ) ^ (98 : ℝ)⌉₊)` becomes `max N₀ 36`, and `1 ≤ kOf N` is obtained from the
proved sharp lemma `AsymptoticsExplicit.kOf_pos` (`36 ≤ N → 1 ≤ kOf N`) instead of the
`2^98` detour through `k_log_ge`. `rfl`-level identity of the statements is checked below.
**No ledger row is closed.**
-/

namespace Paper2.Unit4Shell.T24ActualCut

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.Unit4Shell.T24Actual

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- Same statement as `T24Actual.T24_actual`; the internal `kOf` cutoff is the proved `36`. -/
theorem T24_actual_cut (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) (square : Bool) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      let T : ℕ := if square then
          printedTsq (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length B.degreeBound
            (sourceGap D B) (kOf Φ.val.variables)
        else printedT (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length B.degreeBound
            (sourceGap D B) (kOf Φ.val.variables)
      let a : ℝ := c * (Real.logb 2 T / Real.logb 2 (Real.logb 2 T))
      ∀ {α : Type} [Fintype α] (μ : FiniteLaw α)
        (est : (TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
            B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).output.Tape → α → ℝ),
        letI : Fintype (TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
            B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).output.Tape :=
          (TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
            B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).tapeFintype
        (∀ b, 2 / 3 ≤ μ.prob (fun t => |est b t -
          Workspace.Types.CommComplexity.D
            ((TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
            B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).output.table b).matrix| ≤ a)) →
        (EncodedCNF.Satisfiable Φ.val →
          ((TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
            B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).tapeLaw.prod (μ.iid Amplification.reps)).prob
            (fun x => ¬ Shells.accepts est (TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
            B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).output.budget
              (kOf Φ.val.variables) x) ≤ 1 / 100) ∧
        (¬ EncodedCNF.Satisfiable Φ.val →
          ((TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
            B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).tapeLaw.prod (μ.iid Amplification.reps)).prob
            (fun x => Shells.accepts est (TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
            B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).output.budget
              (kOf Φ.val.variables) x) ≤ (1 / 2) ^ 11 + 1 / 100 ∧
          (1 / 2 : ℝ) ^ 11 + 1 / 100 < 1 / 3) := by
  obtain ⟨N₀, hN₀⟩ := ShellsTight.T24_source_shell D B cs c hc0 hc square
  refine ⟨max N₀ 36, ?_⟩
  intro Φ hsparse hN T a α _ μ est
  letI : Fintype (TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
            B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).output.Tape :=
    (TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
            B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).tapeFintype
  intro hμ
  have hmain := hN₀ Φ hsparse (le_trans (le_max_left _ _) hN)
    (TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
            B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).tapeLaw μ
    (fun b => Workspace.Types.CommComplexity.D
      ((TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
            B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).output.table b).matrix)
    (TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
            B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).output.budget est hμ
  obtain ⟨hm0, _, hinc, hdeg, hloop, hyes, hno⟩ := t10_source D B Φ
  have hΔ : 0 < B.degreeBound := by have := B.degreeBound_pos; omega
  refine ⟨fun hsat => hmain.1 (actual_yes_cost (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound
    (sourceGap D B) (kOf Φ.val.variables) hloop hdeg (source_gap_pos D B) hΔ hm0
    (hyes hsat)), fun hunsat => hmain.2 ?_⟩
  have hk : 1 ≤ kOf Φ.val.variables :=
    AsymptoticsExplicit.kOf_pos _ (le_trans (le_max_right _ _) hN)
  exact actual_no_mass (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound
    (sourceGap D B) (kOf Φ.val.variables) hk hloop hdeg (source_gap_pos D B) hΔ hm0 (hno hunsat)

/-- The two statements are the same proposition (checked by the kernel). -/
example (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) (square : Bool) :
    T24Actual.T24_actual D B cs c hc0 hc square = T24_actual_cut D B cs c hc0 hc square :=
  rfl

#print axioms T24_actual_cut

end Paper2.Unit4Shell.T24ActualCut
