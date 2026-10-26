import EthInapproximability.CurrentPaper.ClockD

/-! Lane owner:b-weighted-level-10, unit 2, segment 4b-ii (third piece): the output words inside
the round clocks.

`output_length`: the admitted bridge output `ProtectedFullBankBridgeScratch.actualPhysicalOutput`
is a `rowMajor` word of length `rows * columns` of `Iteration.step` (its row and column carriers are
in bijection with those of `step` by the admitted `physicalToStepRowEquiv` / `ColEquiv`).
`level_output`: at the physical level `j < k` it is shorter than `4 T` (it has the dimensions of
`physRun (j+1)`, by the admitted `physicalLevel_rows/columns`), and the round's matrix word
`rowMajor (physRun j).matrix.entry` (`mw` in `roundBoundP`) is shorter than `4 T` for `j ≤ k`. -/

namespace EthInapproximability.CurrentPaper.ClockE

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open ClockA

noncomputable section

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem output_length (G : EndpointGraph V E) (c b y j : ℕ) (M : Iteration.Matrix) :
    (ProtectedFullBankBridgeScratch.actualPhysicalOutput G c b y j M).length =
      (Iteration.step G c b y j M).rows * (Iteration.step G c b y j M).columns := by
  unfold ProtectedFullBankBridgeScratch.actualPhysicalOutput
  rw [MatrixMaterialization.rowMajor_length]
  have h1 := Fintype.card_congr (PostProtectedInterlaceScratch.physicalToStepRowEquiv G c b y j M)
  have h2 := Fintype.card_congr (PostProtectedInterlaceScratch.physicalToStepColEquiv G c b y j M)
  simp only [Fintype.card_fin] at h1 h2
  rw [h1, h2]

theorem level_output (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) (j : ℕ)
    (hj : j < ETHTailGrowth.repetitions c A d n) :
    (ProtectedFullBankBridgeScratch.actualPhysicalOutput G c (EffectiveIteration.sourceDepth n)
        (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j)).length <
      4 * FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n := by
  have hf := (level_facts G c A d Δ n γ hcommon hlower hupper hrep (j + 1) hj).1
  rw [output_length]
  have hr := WeightedLevelSameConstructor.physicalLevel_rows G c (EffectiveIteration.sourceDepth n)
    (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
  have hc := WeightedLevelSameConstructor.physicalLevel_columns G c (EffectiveIteration.sourceDepth n)
    (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
  rw [← hr, ← hc]
  exact hf

theorem level_mw (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) (j : ℕ)
    (hj : j ≤ ETHTailGrowth.repetitions c A d n) :
    (MatrixMaterialization.rowMajor
        (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry).length <
      4 * FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n := by
  rw [MatrixMaterialization.rowMajor_length]
  exact (level_facts G c A d Δ n γ hcommon hlower hupper hrep j hj).1

#print axioms output_length
#print axioms level_output
#print axioms level_mw

end
end EthInapproximability.CurrentPaper.ClockE
