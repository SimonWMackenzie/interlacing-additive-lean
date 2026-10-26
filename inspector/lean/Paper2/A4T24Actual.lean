import Paper2.A4ShellsTight

/-!
# Unit 4 (Paper A), segment A4-S10 tightened: T02/T24 on the ACTUAL reduction law
# (owner lane `owner:a-unit4-shell-3`)

Private, 26 September 2026. Production universe. `actual_yes_cost`, `actual_no_mass` and
`T24_actual` are taken from owner-2's UNCHECKPOINTED draft `A4T24Actual.lean` (source SHA-256
in `SHA256SUMS.txt`), copied and compiled in THIS lane (the draft object is not imported).
New here: `T02_actual` (fixed `k`).

The reduction tape law is the ACTUAL `TotalFiniteConstructorScratch.experiment` law of the
T10 graph (its output is `select`, banked `experiment_output_eq_select`), the cost of a tape is
the communication complexity `D` of its printed table, and the budget is the printed budget.
YES premise: banked `selected_yes_cost_le`; NO premise: banked `selected_no_success`. The
ESTIMATOR (law `μ`, reading `est`, accuracy `a`) stays arbitrary: its formal model is the
author's D-A1/D-A3. For T24 the accuracy measure `T` is the scheduled printed count
`printedT`/`printedTsq` (identity with the selected `rows·cols` beyond the public-check cutoff
is NOT stated, predecessor audit note N-1); the sparsity density `cs` is a parameter (D-A2/D-A6).

**None of these statements closes a ledger row** (T02, T24 stay open).
-/

namespace Paper2.Unit4Shell.T24Actual

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics

section Generic

variable {n m : ℕ} (hn : 0 < n) (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)

/-- YES: on a three-colourable source every tape of the actual experiment has cost at most
the printed budget. -/
theorem actual_yes_cost
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m)
    (hcolour : FiniteFallbackOutput.ThreeColourable edge) :
    ∀ t : (TotalFiniteConstructorScratch.experiment hn edge Δ γ k).output.Tape,
      Workspace.Types.CommComplexity.D
          ((TotalFiniteConstructorScratch.experiment hn edge Δ γ k).output.table t).matrix ≤
        (TotalFiniteConstructorScratch.experiment hn edge Δ γ k).output.budget := by
  have h := TotalFiniteConstructorScratch.selected_yes_cost_le hn edge Δ γ k loopless hdegree
    hγ hΔ hm hcolour
  dsimp only at h
  rw [← TotalFiniteConstructorScratch.experiment_output_eq_select hn edge Δ γ k] at h
  exact h

/-- NO: under the actual tape law, the cost misses `budget + k` with probability at most
`2^-11`. -/
theorem actual_no_mass (hk : 1 ≤ k)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m)
    (gap : ∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
      ((Finset.univ.filter (fun e => colour (edge e false) =
        colour (edge e true))).card : ℝ)) :
    @FiniteLaw.prob _ (TotalFiniteConstructorScratch.experiment hn edge Δ γ k).tapeFintype
        (TotalFiniteConstructorScratch.experiment hn edge Δ γ k).tapeLaw
        (fun t => ¬ Workspace.Types.CommComplexity.D
          ((TotalFiniteConstructorScratch.experiment hn edge Δ γ k).output.table t).matrix =
          (TotalFiniteConstructorScratch.experiment hn edge Δ γ k).output.budget + k) ≤
      (1 / 2) ^ 11 := by
  have hs := TotalFiniteConstructorScratch.selected_no_success hn edge Δ γ k hk loopless hdegree
    hγ hΔ hm gap
  letI := (TotalFiniteConstructorScratch.experiment hn edge Δ γ k).tapeFintype
  rw [Amplification.prob_not]
  unfold TotalFiniteConstructorScratch.successProbability at hs
  linarith

end Generic

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- **T24 on the actual source and the actual reduction law (estimator arbitrary).** Beyond an
explicit cutoff, for every sparse valid `Φ` (`clauses ≤ cs·N`) with `k = kOf N`: every
estimator reading the actual tape `b` whose per-run accuracy is `a = c·log₂T/log₂log₂T`
(`c < 1/12`, `T` the rectangular or square printed count) with probability `≥ 2/3` makes the
median-of-147 midpoint test reject a satisfiable `Φ` with probability `≤ 1/100` and accept an
unsatisfiable `Φ` with probability `≤ 2^-11 + 1/100 < 1/3`, where the reduction tape is drawn
from the ACTUAL experiment law of the T10 graph. Does not close a ledger row (T24). -/
theorem T24_actual (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) (square : Bool) :
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
  refine ⟨max N₀ (max 2 ⌈(2 : ℝ) ^ (98 : ℝ)⌉₊), ?_⟩
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
  have hk : 1 ≤ kOf Φ.val.variables := by
    have hN2 : 2 ≤ Φ.val.variables := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
    have hY := logb_ge_of_ge 98 Φ.val.variables
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN)
    have h100 : ((3 * 2 + 1 + 2) / (1 : ℝ) + 1) ^ 2 = 100 := by norm_num
    exact (k_log_ge Φ.val.variables 1 one_pos le_rfl hN2 (by rw [h100]; linarith)).1
  exact actual_no_mass (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound
    (sourceGap D B) (kOf Φ.val.variables) hk hloop hdeg (source_gap_pos D B) hΔ hm0 (hno hunsat)

/-- **T02 on the actual source and the actual reduction law, fixed `k` (estimator arbitrary).**
For every valid `Φ`, every fixed `k ≥ 1` and accuracy `a` with `2a < k`: every estimator
reading the actual reduction tape `b` whose estimate of `D(table b)` is within `a` with
probability `≥ 2/3` makes the median-of-147 midpoint test (threshold `budget + k/2`) reject a
satisfiable `Φ` with probability `≤ 1/100` and accept an unsatisfiable `Φ` with probability
`≤ 2^-11 + 1/100 < 1/3`, the reduction tape being drawn from the ACTUAL experiment law of the
T10 graph of `Φ`. The only open inputs are the estimator (D-A1/D-A3) and the cited records
`D` (X03), `B` (X04). Does not close a ledger row (T02 also needs the machine-level
composition with the estimator and the class statement, D-A4/X06). -/
theorem T02_actual (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (hka : 2 * a < k) (Φ : ValidFormula)
    {α : Type} [Fintype α] (μ : FiniteLaw α)
    (est : (TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) k).output.Tape → α → ℝ) :
    letI : Fintype (TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) k).output.Tape :=
      (TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) k).tapeFintype
    (∀ b, 2 / 3 ≤ μ.prob (fun t => |est b t -
      Workspace.Types.CommComplexity.D
        ((TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) k).output.table b).matrix| ≤ a)) →
    (EncodedCNF.Satisfiable Φ.val →
      ((TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) k).tapeLaw.prod (μ.iid Amplification.reps)).prob
        (fun x => ¬ Shells.accepts est (TotalFiniteConstructorScratch.experiment
          (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) k).output.budget k x) ≤ 1 / 100) ∧
    (¬ EncodedCNF.Satisfiable Φ.val →
      ((TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) k).tapeLaw.prod (μ.iid Amplification.reps)).prob
        (fun x => Shells.accepts est (TotalFiniteConstructorScratch.experiment
          (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) k).output.budget k x) ≤ (1 / 2) ^ 11 + 1 / 100 ∧
      (1 / 2 : ℝ) ^ 11 + 1 / 100 < 1 / 3) := by
  letI : Fintype (TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) k).output.Tape :=
      (TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) k).tapeFintype
  intro hμ
  have h := Shells.T02_error_shell
    (TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
      B.degreeBound (sourceGap D B) k).tapeLaw μ
    (fun b => Workspace.Types.CommComplexity.D
      ((TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) k).output.table b).matrix)
    (TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
      B.degreeBound (sourceGap D B) k).output.budget k a hka est hμ
  obtain ⟨hm0, _, _, hdeg, hloop, hyes, hno⟩ := t10_source D B Φ
  have hΔ : 0 < B.degreeBound := by have := B.degreeBound_pos; omega
  exact ⟨fun hsat => h.1 (actual_yes_cost (t10_vertices_pos D B Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound
      (sourceGap D B) k hloop hdeg (source_gap_pos D B) hΔ hm0 (hyes hsat)),
    fun hunsat => h.2 (actual_no_mass (t10_vertices_pos D B Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound
      (sourceGap D B) k hk hloop hdeg (source_gap_pos D B) hΔ hm0 (hno hunsat))⟩

#print axioms actual_yes_cost
#print axioms actual_no_mass
#print axioms T24_actual
#print axioms T02_actual

end Paper2.Unit4Shell.T24Actual
