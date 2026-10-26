import EthInapproximability.CurrentPaper.IterationAlignedComplete
import EthInapproximability.CurrentPaper.EffectiveIteration

/-!
# The actual finite amplification and its explicit size cutoff

Source: frozen v8 `05-iteration.tex`, `thm:paper-finite-iteration`,
`eq:paper-gap-invariant`, and the finite size part of
`thm:paper-effective-level`. No output profile or one-step hardness assertion
is a hypothesis: the iteration uses the proved literal graph construction.
The final cutoff theorem also discharges all per-level acceptance tests.
This module does not assert a construction-time or ETH conclusion.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.IterationComplete

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open Parameters Iteration EffectiveIteration
open EthInapproximability.ParameterizedNP.GuardedSourceGraph

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- One YES application, including both actual outer interlaces. -/
theorem step_yes (G : EndpointGraph V E) (c b y n : ℕ) (M : Matrix)
    (hnoiso : ∀ v : V, 1 ≤ G.degree v) (hyes : G.SourceYES)
    (hprevious : D M.entry ≤ y) :
    D (step G c b y n M).entry ≤ y + overhead G c b y n M := by
  apply step_yes_upper G c b y n M
  exact (ProtectedIterationBounds.yes_upper G c b y n M hnoiso hyes).trans
    (Nat.add_le_add_right hprevious _)

/-- One NO application, including restoration of the two-bound invariant
and the stronger three-bound output. No constructed-matrix profile is a
hypothesis. -/
theorem step_no (G : EndpointGraph V E) (c b y n : ℕ) (M : Matrix)
    (hc : 0 < c) (ha : Accepted (parameters G c b y n M))
    (hf : IsRobustAt M.entry b) (hcost : D M.entry = y + n) (hminimum : 3 ≤ y + n)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hcommon : G.SourceCommon γ Δ) (hno : G.SourceNO γ)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ c) :
    D (step G c b y n M).entry = y + n + overhead G c b y n M + 1 ∧
    IsRobustAt (step G c b y n M).entry b ∧
    y + n + overhead G c b y n M + 1 ≤
      LambdaGE (step G c b y n M).entry 1 (2 ^ (-(b : ℝ))) (3 / 5) :=
  step_no_of_profiles G c b y n M hc hf.1 hminimum
    (IterationAlignedComplete.aligned_profiles G c b y n M hc ha hf hcost
      hΔ hγ hγone hcommon hno hsource)

/-- The YES induction uses a genuine legal packing of this graph at every
level. No communication upper bound is supplied for the constructed matrices. -/
theorem run_yes (G : EndpointGraph V E) (c b : ℕ) (initial : State) (k : ℕ)
    (hnoiso : ∀ v : V, 1 ≤ G.degree v) (hyes : G.SourceYES)
    (hinitial : D initial.matrix.entry ≤ initial.budget) :
    ∀ j ≤ k, D (run G c b initial j).matrix.entry ≤ (run G c b initial j).budget := by
  apply Iteration.run_yes G c b initial k hinitial
  intro j _ hprevious
  exact (ProtectedIterationBounds.yes_upper G c b (run G c b initial j).budget j
    (run G c b initial j).matrix hnoiso hyes).trans (Nat.add_le_add_right hprevious _)

/-- Every NO step derives its four aligned profiles from the previous exact
cost and two-bound robustness. Only the printed numerical acceptance tests
remain in this arbitrary-initial-matrix version. -/
theorem run_no (G : EndpointGraph V E) (c b : ℕ) (initial : State) (k : ℕ)
    (hc : 0 < c) (hb : 1 ≤ b)
    (hcost : D initial.matrix.entry = initial.budget)
    (hrobust : IsRobustAt initial.matrix.entry b)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hcommon : G.SourceCommon γ Δ) (hno : G.SourceNO γ)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ c)
    (haccepted : ∀ j < k, Accepted (runParameters G c b initial j))
    (hminimum : ∀ j < k, 3 ≤ (run G c b initial j).budget + j) :
    ∀ j ≤ k,
      D (run G c b initial j).matrix.entry = (run G c b initial j).budget + j ∧
      IsRobustAt (run G c b initial j).matrix.entry b := by
  apply Iteration.run_no G c b initial k hc hb hcost hrobust hminimum
  intro j hj hprevious hrobustPrevious
  exact IterationAlignedComplete.aligned_profiles G c b (run G c b initial j).budget j
    (run G c b initial j).matrix hc (haccepted j hj) hrobustPrevious hprevious
    hΔ hγ hγone hcommon hno hsource

/-- The additional three-bound statement is an output of every positive
level, not an assumption replacing the two-bound induction invariant. -/
theorem run_no_lambda (G : EndpointGraph V E) (c b : ℕ) (initial : State) (k : ℕ)
    (hc : 0 < c) (hb : 1 ≤ b)
    (hcost : D initial.matrix.entry = initial.budget)
    (hrobust : IsRobustAt initial.matrix.entry b)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hcommon : G.SourceCommon γ Δ) (hno : G.SourceNO γ)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ c)
    (haccepted : ∀ j < k, Accepted (runParameters G c b initial j))
    (hminimum : ∀ j < k, 3 ≤ (run G c b initial j).budget + j) :
    ∀ j, 1 ≤ j → j ≤ k →
      (run G c b initial j).budget + j ≤
        LambdaGE (run G c b initial j).matrix.entry 1 (2 ^ (-(b : ℝ))) (3 / 5) := by
  apply Iteration.run_no_lambda G c b initial k hc hb hcost hrobust hminimum
  intro j hj hprevious hrobustPrevious
  exact IterationAlignedComplete.aligned_profiles G c b (run G c b initial j).budget j
    (run G c b initial j).matrix hc (haccepted j hj) hrobustPrevious hprevious
    hΔ hγ hγone hcommon hno hsource

/-- The manuscript's literal indexing seed supplies all initial invariants. -/
theorem indexing_no (G : EndpointGraph V E) (c b k : ℕ)
    (hc : 0 < c) (hb : 1 ≤ b)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hcommon : G.SourceCommon γ Δ) (hno : G.SourceNO γ)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ c)
    (haccepted : ∀ j < k, Accepted (runParameters G c b (seedState b) j)) :
    ∀ j ≤ k,
      D (run G c b (seedState b) j).matrix.entry = (run G c b (seedState b) j).budget + j ∧
      IsRobustAt (run G c b (seedState b) j).matrix.entry b ∧
      (run G c b (seedState b) j).budget + j ≤
        LambdaGE (run G c b (seedState b) j).matrix.entry 1 (2 ^ (-(b : ℝ))) (3 / 5) := by
  apply Iteration.run_indexing_no G c b k hc hb
  intro j hj hprevious hrobustPrevious
  exact IterationAlignedComplete.aligned_profiles G c b (run G c b (seedState b) j).budget j
    (run G c b (seedState b) j).matrix hc (haccepted j hj) hrobustPrevious hprevious
    hΔ hγ hγone hcommon hno hsource

theorem indexing_yes (G : EndpointGraph V E) (c b k : ℕ)
    (hnoiso : ∀ v : V, 1 ≤ G.degree v) (hyes : G.SourceYES) :
    ∀ j ≤ k, D (run G c b (seedState b) j).matrix.entry ≤
      (run G c b (seedState b) j).budget :=
  run_yes G c b (seedState b) k hnoiso hyes (seedMatrix_cost b).le

theorem sourceDepth_pos (n : ℕ) : 1 ≤ sourceDepth n :=
  Nat.clog_pos (by decide) (by omega)

/-- Actual fixed-graph finite gap and table size, beyond the single explicit
total cutoff. The same promise-independent sequence is used for both cases.
Neither output profiles, numerical acceptance nor a cutoff-existence oracle
remain as assumptions. Runtime is intentionally not asserted here. -/
theorem finite_gap_and_size (G : EndpointGraph V E) (c A d n k : ℕ)
    (hk : 0 < k) (hcut : sourceCutoff c A d k ≤ n)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hcommon : G.SourceCommon γ Δ)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ c)
    (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * sourceDepth n ^ d) :
    let b := sourceDepth n
    let states := run G c b (seedState b)
    (G.SourceYES → ∀ j ≤ k, D (states j).matrix.entry ≤ (states j).budget) ∧
    (G.SourceNO γ → ∀ j ≤ k,
      D (states j).matrix.entry = (states j).budget + j ∧
      IsRobustAt (states j).matrix.entry b ∧
      (states j).budget + j ≤ LambdaGE (states j).matrix.entry 1 (2 ^ (-(b : ℝ))) (3 / 5)) ∧
    (∀ j ≤ k, ((states j).matrix.rows * (states j).matrix.columns) ^ k < 2 ^ n) ∧
    (∀ j ≤ k, 2 * k * ((states j).budget + j) < n) := by
  let b := sourceDepth n
  let states := run G c b (seedState b)
  have hv : Fintype.card V ≤ 2 * Fintype.card E :=
    G.card_vertex_le_two_mul_card_edge (fun v => (hcommon.2 v).1)
  have hc : 0 < c := lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ) ^ 24)
    (IterationAlignedComplete.source_constant_floor hΔ hγ hγone hsource)
  have haccepted := run_indexing_beyond_cutoff G c A d n k hcut hv hlower hupper
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hyes
    exact indexing_yes G c b k (fun v => (hcommon.2 v).1) hyes
  · intro hno
    exact indexing_no G c b k hc (sourceDepth_pos n) hΔ hγ hγone hcommon hno hsource
      (fun j hj => (haccepted j hj).1)
  · intro j hj
    exact (run_indexing_table_size_beyond_cutoff G c A d n k hk hcut hv hlower hupper j hj).2
  · intro j hj
    have h := run_indexing_budget_beyond_cutoff G c A d n k hk hcut hv hlower hupper j hj
    change 2 * k * ((states j).budget + j + j) < n at h
    exact (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans_lt h

end EthInapproximability.CurrentPaper.IterationComplete
