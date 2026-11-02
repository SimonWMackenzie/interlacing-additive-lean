import EthInapproximability.CurrentPaper.ClockE

/-! Lane owner:b-weighted-level-10, unit 2, segment 4b-ii (fourth piece): the bridge carriers.

`actualRows G c b y j M = |NRow|` and `actualCols = |NCol|` (admitted
`ProtectedFullBankBridgeScratch`) are at most the row / column count of `Iteration.step`
(`|OutputRow| = (2^rq |NRow|)^(2^rQ)`, `|OutputCol| = 2^rQ |NCol|^(2^rq)`), hence, at the physical
level `j < k`, below `4 T`. They enter `readyBound`/`prepBoundJ` and the bridge clocks. -/

namespace EthInapproximability.CurrentPaper.ClockF

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open ClockA

noncomputable section

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem actualRows_le (G : EndpointGraph V E) (c b y j : ℕ) (M : Iteration.Matrix) :
    ProtectedFullBankBridgeScratch.actualRows G c b y j M ≤ (Iteration.step G c b y j M).rows := by
  have h2 := Fintype.card_congr (Iteration.outputRowNumbering G c b y j M).equiv
  simp only [Fintype.card_fin] at h2
  show Fintype.card (Iteration.NRow G c b y j M) ≤ (Iteration.outputRowNumbering G c b y j M).size
  rw [h2]
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
  have key : ∀ (x p q : ℕ), x ≤ (2 ^ p * x) ^ (2 ^ q) := fun x p q =>
    le_trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
      (Nat.le_self_pow (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)) _)
  exact key _ _ _

theorem actualCols_le (G : EndpointGraph V E) (c b y j : ℕ) (M : Iteration.Matrix) :
    ProtectedFullBankBridgeScratch.actualCols G c b y j M ≤ (Iteration.step G c b y j M).columns := by
  have h2 := Fintype.card_congr (Iteration.outputColNumbering G c b y j M).equiv
  simp only [Fintype.card_fin] at h2
  show Fintype.card (Iteration.NCol G c b y j M) ≤ (Iteration.outputColNumbering G c b y j M).size
  rw [h2]
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
  calc Fintype.card (Iteration.NCol G c b y j M)
      ≤ Fintype.card (Iteration.NCol G c b y j M) ^ 2 ^ Iteration.rq G c b y j M :=
        Nat.le_self_pow (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)) _
    _ ≤ _ := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)

theorem level_actual (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) (j : ℕ)
    (hj : j < ETHTailGrowth.repetitions c A d n) :
    ProtectedFullBankBridgeScratch.actualRows G c (EffectiveIteration.sourceDepth n)
        (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j) <
      4 * FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ∧
    ProtectedFullBankBridgeScratch.actualCols G c (EffectiveIteration.sourceDepth n)
        (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j) <
      4 * FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n := by
  have hf := (level_facts G c A d Δ n γ hcommon hlower hupper hrep (j + 1) hj).1
  have hr := WeightedLevelSameConstructor.physicalLevel_rows G c (EffectiveIteration.sourceDepth n)
    (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
  have hc := WeightedLevelSameConstructor.physicalLevel_columns G c (EffectiveIteration.sourceDepth n)
    (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
  have ha := actualRows_le G c (EffectiveIteration.sourceDepth n)
    (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
  have hb := actualCols_le G c (EffectiveIteration.sourceDepth n)
    (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
  rw [← hr] at ha
  rw [← hc] at hb
  have hr1 := rows_le_prod (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)) (j + 1)).matrix
  have hc1 := cols_le_prod (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)) (j + 1)).matrix
  change _ ≤ (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)) (j + 1)).matrix.rows at ha
  change _ ≤ (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)) (j + 1)).matrix.columns at hb
  constructor <;> omega

#print axioms actualRows_le
#print axioms actualCols_le
#print axioms level_actual

end
end EthInapproximability.CurrentPaper.ClockF
