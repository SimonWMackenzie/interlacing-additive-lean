import EthInapproximability.CurrentPaper.DimsClock1Bound
import EthInapproximability.CurrentPaper.W12Final2

/-! Lane owner:b-dims-clock-1, segment 3: `BLevel12.DimsPoly` (lane owner-12, `W12Final2`) holds, with
the constants `Cx = 81 Kd`, `ex = 0`, `fx = 2`, for every `c A d Δ γ` satisfying the source-constant
hypotheses.

At the inputs of ANY step (`dims_step`): the admitted `NextDimsEmbedTN.rows_identity` /
`cols_identity` identify the two outputs with `nextRows P` / `nextColumns P |V|`, which the admitted
`EffectiveIteration.step_exact_counts` identifies with the row / column count of `Iteration.step`,
positive by the admitted `Iteration.Matrix.rows_pos` / `columns_pos`; `x.c` is the source constant.
At the physical level `j < k` (`step_lt`): these counts are those of `physRun (j+1)` (admitted
`WeightedLevelSameConstructor.physicalLevel_rows/columns`), below `4 T` by the admitted
`ClockA.level_facts (j+1)` (exactly as in the admitted `ClockF.level_actual`). Level 0 is the step at
`j = 0` (`yP G c b 0`, `MP G c b 0` are the seed's budget and matrix). `1 ≤ c` is the admitted
`ClockA.hc_of_source`. -/

namespace EthInapproximability.CurrentPaper.DimsClock1

open EthInapproximability.ParameterizedNP.GuardedSourceGraph

noncomputable section

set_option maxHeartbeats 4000000

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The admitted dims clock at the inputs of any step, by the step's output dimensions. -/
theorem dims_step (G : EndpointGraph V E) (c b y j : ℕ) (M : Iteration.Matrix) (hc : 1 ≤ c) :
    NextDimsMachineTN.dimsBound (NextDimsEmbedTN.dimsIn (Iteration.stepParameters G c b y j M)
        (Fintype.card V) (Parameters.bins (Iteration.stepParameters G c b y j M) *
          EffectiveIteration.familySize (Iteration.stepParameters G c b y j M))) ≤
      Kd * ((Iteration.step G c b y j M).rows + (Iteration.step G c b y j M).columns + 1) ^ 2 := by
  obtain ⟨hr, hcl⟩ := EffectiveIteration.step_exact_counts G c b y j M
  have hr' : NextDimsMachineTN.rowsOut (NextDimsEmbedTN.dimsIn (Iteration.stepParameters G c b y j M)
      (Fintype.card V) (Parameters.bins (Iteration.stepParameters G c b y j M) *
        EffectiveIteration.familySize (Iteration.stepParameters G c b y j M))) =
      (Iteration.step G c b y j M).rows := by
    rw [NextDimsEmbedTN.rows_identity]; exact hr.symm
  have hc' : NextDimsMachineTN.colsOut (NextDimsEmbedTN.dimsIn (Iteration.stepParameters G c b y j M)
      (Fintype.card V) (Parameters.bins (Iteration.stepParameters G c b y j M) *
        EffectiveIteration.familySize (Iteration.stepParameters G c b y j M))) =
      (Iteration.step G c b y j M).columns := by
    rw [NextDimsEmbedTN.cols_identity]; exact hcl.symm
  have hR : 1 ≤ NextDimsMachineTN.rowsOut (NextDimsEmbedTN.dimsIn (Iteration.stepParameters G c b y j M)
      (Fintype.card V) (Parameters.bins (Iteration.stepParameters G c b y j M) *
        EffectiveIteration.familySize (Iteration.stepParameters G c b y j M))) := by
    rw [hr']; exact (Iteration.step G c b y j M).rows_pos
  have hC : 1 ≤ NextDimsMachineTN.colsOut (NextDimsEmbedTN.dimsIn (Iteration.stepParameters G c b y j M)
      (Fintype.card V) (Parameters.bins (Iteration.stepParameters G c b y j M) *
        EffectiveIteration.familySize (Iteration.stepParameters G c b y j M))) := by
    rw [hc']; exact (Iteration.step G c b y j M).columns_pos
  have h := dimsBound_le_sq _ hR hC hc
  rw [hr', hc'] at h
  exact h

#print axioms dims_step

/-- At the physical level `j < k` the step's output dimensions are below `4 T`. -/
theorem step_lt (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) (j : ℕ)
    (hj : j < ETHTailGrowth.repetitions c A d n) :
    (Iteration.step G c (EffectiveIteration.sourceDepth n)
        (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j)).rows <
      4 * FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ∧
    (Iteration.step G c (EffectiveIteration.sourceDepth n)
        (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j)).columns <
      4 * FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n := by
  have hf := (ClockA.level_facts G c A d Δ n γ hcommon hlower hupper hrep (j + 1) hj).1
  have hr := WeightedLevelSameConstructor.physicalLevel_rows G c (EffectiveIteration.sourceDepth n)
    (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
  have hc := WeightedLevelSameConstructor.physicalLevel_columns G c (EffectiveIteration.sourceDepth n)
    (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
  have hr1 := ClockA.rows_le_prod (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)) (j + 1)).matrix
  have hc1 := ClockA.cols_le_prod (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)) (j + 1)).matrix
  have e1 : (Iteration.step G c (EffectiveIteration.sourceDepth n)
      (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
      (StepP.MP G c (EffectiveIteration.sourceDepth n) j)).rows =
      (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)) (j + 1)).matrix.rows := hr.symm
  have e2 : (Iteration.step G c (EffectiveIteration.sourceDepth n)
      (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
      (StepP.MP G c (EffectiveIteration.sourceDepth n) j)).columns =
      (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)) (j + 1)).matrix.columns := hc.symm
  constructor <;> omega

#print axioms step_lt

theorem shape (K r s T a : ℕ) (hr : r < 4 * T) (hs : s < 4 * T) :
    K * (r + s + 1) ^ 2 ≤ 81 * K * a ^ 0 * T ^ 2 := by
  have h1 : r + s + 1 ≤ 9 * T := by omega
  have h2 : (r + s + 1) ^ 2 ≤ (9 * T) ^ 2 := Nat.pow_le_pow_left h1 2
  calc K * (r + s + 1) ^ 2 ≤ K * (9 * T) ^ 2 := Nat.mul_le_mul_left _ h2
    _ = 81 * K * a ^ 0 * T ^ 2 := by ring

/-- **Segment 3.** `BLevel12.DimsPoly` holds for every `c A d Δ γ` satisfying the source-constant
hypotheses, with `Cx = 81 Kd`, `ex = 0`, `fx = 2`. -/
theorem dimsPoly_holds (c A d Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ c) :
    BLevel12.DimsPoly c A d Δ γ (81 * Kd) 0 2 := by
  have hc : 1 ≤ c := ClockA.hc_of_source hΔ hγ hγone hsource
  intro V E _ _ _ _ G n hcommon hlower hupper hrep
  refine ⟨?_, ?_⟩
  · have h0 := step_lt G c A d Δ n γ hcommon hlower hupper hrep 0 (by omega)
    exact (dims_step G c (EffectiveIteration.sourceDepth n)
      (StepP.yP G c (EffectiveIteration.sourceDepth n) 0) 0
      (StepP.MP G c (EffectiveIteration.sourceDepth n) 0) hc).trans (shape _ _ _ _ _ h0.1 h0.2)
  · intro j _ hj
    have h := step_lt G c A d Δ n γ hcommon hlower hupper hrep j hj
    exact (dims_step G c (EffectiveIteration.sourceDepth n)
      (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
      (StepP.MP G c (EffectiveIteration.sourceDepth n) j) hc).trans (shape _ _ _ _ _ h.1 h.2)

#print axioms dimsPoly_holds

/-- The premise `hD` of lane owner-12's `W12Final3` endpoints, discharged. -/
theorem hD_holds : ∀ (c A d Δ : ℕ) (γ : ℚ), 0 < Δ → 0 < γ → γ ≤ 1 → 2 ^ 44 * (Δ : ℚ) / γ ≤ c →
    ∃ Cx ex fx : ℕ, BLevel12.DimsPoly c A d Δ γ Cx ex fx :=
  fun c A d Δ γ hΔ hγ hγone hsource => ⟨81 * Kd, 0, 2, dimsPoly_holds c A d Δ γ hΔ hγ hγone hsource⟩

#print axioms hD_holds

end
end EthInapproximability.CurrentPaper.DimsClock1
