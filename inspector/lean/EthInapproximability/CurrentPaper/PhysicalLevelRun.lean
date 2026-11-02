import EthInapproximability.CurrentPaper.WeightedLevelSameConstructor
import EthInapproximability.CurrentPaper.IterationComplete
import EthInapproximability.CurrentPaper.BitMachineBankCodec
import EthInapproximability.CurrentPaper.ETHTailGrowth
import EthInapproximability.CurrentPaper.FinalPadding
import EthInapproximability.CurrentPaper.SourceOriginalBranchPackets
import EthInapproximability.CurrentPaper.EncodedETHSource

/-! Lane owner:b-weighted-level-3, unit 2, segment 3b (root decision of
25 September 21:05: the GENERALIZED-NUMBERING RUN).

`physRun` is the physical k-round sequence: level `j+1` is the admitted
physical step (`WeightedLevelSameConstructor.physicalLevel`, i.e.
`Iteration.number (Iteration.rawOutput ...) physRowNumbering physColNumbering`,
the word the admitted `actual_physical_step_run` writes) applied to the
PHYSICALLY numbered level `j`, with the same public budget recursion as
`Iteration.run`.

Transport (no renumbering stage): the per-level lemmas that
`IterationComplete.finite_gap_and_size` uses (`IterationComplete.step_yes`,
`IterationComplete.step_no`) are stated for an ARBITRARY matrix `M`; the
numbering-invariance of `D`, robustness and `LambdaGE`
(`Iteration.number_cost/robust/lambda`) is reused through the frozen
`WeightedLevelSameConstructor.physicalLevel_cost/robust/lambda`; and
`Iteration.parameters` (hence acceptance, `overhead`, the next dimensions via
`EffectiveIteration.step_next_parameters`) depends on the matrix only through
its dimensions. So the physical parameter sequence equals
`EffectiveIteration.runParameters` at every level (`physParameters_eq`), the
public budgets, rows and columns coincide with `Iteration.run`'s, and every
gap and size conclusion of `finite_gap_and_size` holds for `physRun`
(`physical_finite_gap_and_size`). `HB2Physical` states the unit-4 H-B2
interface (unit4-compositions-map MAP section 1.5) for this sequence.

NOT claimed: any machine producing `physRun` (that is `HB2Physical`, an
interface Prop, not proved here); `physRun = Iteration.run` literally. -/

namespace EthInapproximability.CurrentPaper.PhysicalLevelRun

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open Iteration EffectiveIteration

noncomputable section

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The physical k-round sequence: each level is the admitted physical step
applied to the physically numbered previous level; the public budget is
Iteration's recursion `y ↦ y + overhead`. -/
def physRun (G : EndpointGraph V E) (c b : ℕ) (initial : State) : ℕ → State
  | 0 => initial
  | j + 1 =>
    let current := physRun G c b initial j
    ⟨WeightedLevelSameConstructor.physicalLevel G c b current.budget j current.matrix,
      current.budget + overhead G c b current.budget j current.matrix⟩

section Transport

variable (G : EndpointGraph V E) (c b : ℕ) (initial : State)

@[simp] theorem physRun_zero : physRun G c b initial 0 = initial := rfl

theorem physRun_succ_matrix (j : ℕ) :
    (physRun G c b initial (j + 1)).matrix =
      WeightedLevelSameConstructor.physicalLevel G c b (physRun G c b initial j).budget j
        (physRun G c b initial j).matrix := rfl

theorem physRun_succ_budget (j : ℕ) :
    (physRun G c b initial (j + 1)).budget =
      (physRun G c b initial j).budget +
        overhead G c b (physRun G c b initial j).budget j (physRun G c b initial j).matrix :=
  rfl

/-- `Iteration.parameters` reads the matrix only through its dimensions. -/
theorem parameters_congr (y i : ℕ) (M N : Matrix)
    (hr : M.rows = N.rows) (hc : M.columns = N.columns) :
    parameters G c b y i M = parameters G c b y i N := by
  unfold parameters
  rw [hr, hc]

theorem physicalLevel_parameters (y i y' i' : ℕ) (M : Matrix) :
    parameters G c b y' i' (WeightedLevelSameConstructor.physicalLevel G c b y i M) =
      parameters G c b y' i' (step G c b y i M) :=
  parameters_congr G c b y' i' _ _
    (WeightedLevelSameConstructor.physicalLevel_rows G c b y i M)
    (WeightedLevelSameConstructor.physicalLevel_columns G c b y i M)

/-- The parameter record of the physical sequence at level `j`. -/
def physParameters (j : ℕ) : Parameters.Input :=
  parameters G c b (physRun G c b initial j).budget j (physRun G c b initial j).matrix

theorem physParameters_succ (j : ℕ) :
    physParameters G c b initial (j + 1) =
      nextInput (physParameters G c b initial j) (Fintype.card V) := by
  unfold physParameters
  rw [physRun_succ_budget, physRun_succ_matrix, physicalLevel_parameters]
  exact step_next_parameters G c b _ j _

/-- The physical parameter sequence is literally `runParameters`. -/
theorem physParameters_eq (j : ℕ) :
    physParameters G c b initial j = runParameters G c b initial j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [physParameters_succ, ih, runParameters_succ]

/-- Same public budget `y_j` as `Iteration.run` at every level. -/
theorem physRun_budget_eq (j : ℕ) :
    (physRun G c b initial j).budget = (run G c b initial j).budget := by
  have h := congrArg Parameters.Input.cost (physParameters_eq G c b initial j)
  change (physRun G c b initial j).budget + j = (run G c b initial j).budget + j at h
  omega

theorem physRun_rows_eq (j : ℕ) :
    (physRun G c b initial j).matrix.rows = (run G c b initial j).matrix.rows :=
  congrArg Parameters.Input.rows (physParameters_eq G c b initial j)

theorem physRun_columns_eq (j : ℕ) :
    (physRun G c b initial j).matrix.columns = (run G c b initial j).matrix.columns :=
  congrArg Parameters.Input.columns (physParameters_eq G c b initial j)

/-- YES invariant for the physical sequence (admitted `step_yes` on the
physical matrix, transported through `physicalLevel_cost`). -/
theorem physRun_yes (hnoiso : ∀ v : V, 1 ≤ G.degree v) (hyes : G.SourceYES)
    (hinitial : D initial.matrix.entry ≤ initial.budget) :
    ∀ j, D (physRun G c b initial j).matrix.entry ≤ (physRun G c b initial j).budget := by
  intro j
  induction j with
  | zero => exact hinitial
  | succ j ih =>
    rw [physRun_succ_matrix, physRun_succ_budget, WeightedLevelSameConstructor.physicalLevel_cost]
    exact IterationComplete.step_yes G c b _ j _ hnoiso hyes ih

end Transport

/-- NO invariant (exact cost, robustness, three-bound profile) for the
physical sequence from the indexing seed; the per-level acceptance premise
is the SAME one `IterationComplete.indexing_no` takes, about
`runParameters`. -/
theorem physRun_indexing_no (G : EndpointGraph V E) (c b k : ℕ)
    (hc : 0 < c) (hb : 1 ≤ b)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hcommon : G.SourceCommon γ Δ) (hno : G.SourceNO γ)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ c)
    (haccepted : ∀ j < k, Parameters.Accepted (runParameters G c b (seedState b) j)) :
    ∀ j ≤ k,
      D (physRun G c b (seedState b) j).matrix.entry =
          (physRun G c b (seedState b) j).budget + j ∧
      IsRobustAt (physRun G c b (seedState b) j).matrix.entry b ∧
      (physRun G c b (seedState b) j).budget + j ≤
        LambdaGE (physRun G c b (seedState b) j).matrix.entry 1 (2 ^ (-(b : ℝ))) (3 / 5) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_⟩
    · change D (seedMatrix b).entry = IndexSeed.exponent b + 1 + 0
      rw [seedMatrix_cost]
    · exact seedMatrix_robust b hb
    · change IndexSeed.exponent b + 1 + 0 ≤
        LambdaGE (seedMatrix b).entry 1 (2 ^ (-(b : ℝ))) (3 / 5)
      rw [Nat.add_zero]
      exact seedMatrix_lambda b
  | succ j ih =>
    intro hj
    obtain ⟨hcost, hrob, _⟩ := ih (by omega)
    have hacc : Parameters.Accepted (parameters G c b (physRun G c b (seedState b) j).budget j
        (physRun G c b (seedState b) j).matrix) := by
      have h := haccepted j (by omega)
      rw [← physParameters_eq] at h
      exact h
    have hmin : 3 ≤ (physRun G c b (seedState b) j).budget + j := by
      rw [physRun_budget_eq]
      have h1 := seedState_minimum b
      have h2 := run_budget_ge_initial G c b (seedState b) j
      omega
    obtain ⟨h1, h2, h3⟩ := IterationComplete.step_no G c b _ j _ hc hacc hrob hcost hmin
      hΔ hγ hγone hcommon hno hsource
    rw [physRun_succ_matrix, physRun_succ_budget, WeightedLevelSameConstructor.physicalLevel_cost,
      WeightedLevelSameConstructor.physicalLevel_robust,
      WeightedLevelSameConstructor.physicalLevel_lambda]
    refine ⟨?_, h2, ?_⟩
    · rw [h1]
      omega
    · omega

/-- Unit-2 endpoint for the physical sequence (segment 3b): the SAME
hypotheses and the SAME gap and size conclusions as
`IterationComplete.finite_gap_and_size`, for `physRun` in place of
`Iteration.run`, plus the identity of the public budgets `y_j`, rows and
columns with `Iteration.run`'s. -/
theorem physical_finite_gap_and_size (G : EndpointGraph V E) (c A d n k : ℕ)
    (hk : 0 < k) (hcut : sourceCutoff c A d k ≤ n)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hcommon : G.SourceCommon γ Δ)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ c)
    (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * sourceDepth n ^ d) :
    let b := sourceDepth n
    let states := physRun G c b (seedState b)
    (∀ j, (states j).budget = (run G c b (seedState b) j).budget ∧
      (states j).matrix.rows = (run G c b (seedState b) j).matrix.rows ∧
      (states j).matrix.columns = (run G c b (seedState b) j).matrix.columns) ∧
    (G.SourceYES → ∀ j ≤ k, D (states j).matrix.entry ≤ (states j).budget) ∧
    (G.SourceNO γ → ∀ j ≤ k,
      D (states j).matrix.entry = (states j).budget + j ∧
      IsRobustAt (states j).matrix.entry b ∧
      (states j).budget + j ≤ LambdaGE (states j).matrix.entry 1 (2 ^ (-(b : ℝ))) (3 / 5)) ∧
    (∀ j ≤ k, ((states j).matrix.rows * (states j).matrix.columns) ^ k < 2 ^ n) ∧
    (∀ j ≤ k, 2 * k * ((states j).budget + j) < n) := by
  intro b states
  have hv : Fintype.card V ≤ 2 * Fintype.card E :=
    G.card_vertex_le_two_mul_card_edge (fun v => (hcommon.2 v).1)
  have hc : 0 < c := lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ) ^ 24)
    (IterationAlignedComplete.source_constant_floor hΔ hγ hγone hsource)
  have haccepted := run_indexing_beyond_cutoff G c A d n k hcut hv hlower hupper
  have hgap := IterationComplete.finite_gap_and_size G c A d n k hk hcut hΔ hγ hγone hcommon
    hsource hlower hupper
  dsimp only at hgap
  obtain ⟨_, _, hsize, hbudget⟩ := hgap
  refine ⟨fun j => ⟨physRun_budget_eq G c b _ j, physRun_rows_eq G c b _ j,
    physRun_columns_eq G c b _ j⟩, ?_, ?_, ?_, ?_⟩
  · intro hyes j _
    exact physRun_yes G c b (seedState b) (fun v => (hcommon.2 v).1) hyes
      (seedMatrix_cost b).le j
  · intro hno
    exact physRun_indexing_no G c b k hc (IterationComplete.sourceDepth_pos n) hΔ hγ hγone
      hcommon hno hsource (fun j hj => (haccepted j hj).1)
  · intro j hj
    change ((physRun G c b (seedState b) j).matrix.rows *
      (physRun G c b (seedState b) j).matrix.columns) ^ k < 2 ^ n
    rw [physRun_rows_eq, physRun_columns_eq]
    exact hsize j hj
  · intro j hj
    change 2 * k * ((physRun G c b (seedState b) j).budget + j) < n
    rw [physRun_budget_eq]
    exact hbudget j hj

/-- The unit-4 H-B2 interface (unit4-compositions-map MAP section 1.5),
stated for the PHYSICAL sequence: one fixed machine maps the branch packet of
`n` and the encoded graph to the bank of unary `n`, unary `k`, unary rows,
unary columns, the row-major word of `physRun ... k` and unary `y_k`, within
the public clock. By `physical_finite_gap_and_size`, `y_k`, rows and columns
are the numbers of `Iteration.run`, and the gap/size conclusions hold for the
emitted matrix. This is an interface Prop; it is NOT proved here. -/
def HB2Physical (c A d Δ : ℕ) (γ : ℚ) : Prop :=
  ∃ (Mtab : BitMachine.Machine) (C₂ E₂ F₂ : ℕ),
    ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : EndpointGraph V E) (n : ℕ),
      G.SourceCommon γ Δ → n ≤ Fintype.card E →
      Fintype.card E ≤ A * n * sourceDepth n ^ d →
      1 ≤ ETHTailGrowth.repetitions c A d n →
      let k := ETHTailGrowth.repetitions c A d n
      let b := sourceDepth n
      let st := physRun G c b (seedState b) k
      let w := SourceOriginalBranchPackets.packet n
        (EncodedGraph.encode (EncodedETHSource.serializeGraph G))
      Mtab.OutputsWithin w
        (BitMachineBankCodec.encode ![List.replicate n true, List.replicate k true,
          List.replicate st.matrix.rows true, List.replicate st.matrix.columns true,
          MatrixMaterialization.rowMajor st.matrix.entry, List.replicate st.budget true])
        (C₂ * (w.length + 1) ^ E₂ *
          FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ F₂)

#print axioms physParameters_eq
#print axioms physRun_budget_eq
#print axioms physRun_yes
#print axioms physRun_indexing_no
#print axioms physical_finite_gap_and_size

end
end EthInapproximability.CurrentPaper.PhysicalLevelRun
