import EthInapproximability.CurrentPaper.ClockF

/-! Lane owner:b-weighted-level-10, unit 2, segment 4b-ii (fifth piece): the public widths are
below `n` at every round level `i < k`.

The admitted cutoff selection `CutoffBitMachine.actualClock_selected_levels` gives
`2 k · oneLevelBound (runParameters i) < n` for `i < k`, and the admitted
`EffectiveIteration.balanceOrder_le_oneLevelBound` gives `balanceOrder ≤ oneLevelBound`. Since
`firstExponent = 256 scale^2` and `outerExponent = 1000 scale^2` are at most
`balanceExponent = 10^8 scale^4`, the widths `2^firstExponent` (the `4·2^(S x (w 3))` terms of
owner-7's `dimsBound`), `outerWidth` and `balanceOrder` of the physical level-`i` parameters are all
below `n` (`level_widths`). This removes the caution recorded in the checkpoint for levels `i < k`. -/

namespace EthInapproximability.CurrentPaper.ClockG

open EthInapproximability.ParameterizedNP.GuardedSourceGraph

noncomputable section

theorem scale_pos (P : Parameters.Input) : 1 ≤ Parameters.scale P := by
  unfold Parameters.scale
  have : 1 ≤ 2 ^ 24 := Nat.one_le_two_pow
  exact le_trans this (le_max_left _ _)

theorem firstExponent_le (P : Parameters.Input) :
    Parameters.firstExponent P ≤ Parameters.balanceExponent P := by
  unfold Parameters.firstExponent Parameters.balanceExponent
  have h := scale_pos P
  have h2 : Parameters.scale P ^ 2 ≤ Parameters.scale P ^ 4 := Nat.pow_le_pow_right h (by norm_num)
  omega

theorem outerExponent_le (P : Parameters.Input) :
    Parameters.outerExponent P ≤ Parameters.balanceExponent P := by
  unfold Parameters.outerExponent Parameters.balanceExponent
  have h := scale_pos P
  have h2 : Parameters.scale P ^ 2 ≤ Parameters.scale P ^ 4 := Nat.pow_le_pow_right h (by norm_num)
  omega

theorem widths_le (P : Parameters.Input) :
    2 ^ Parameters.firstExponent P ≤ Parameters.balanceOrder P ∧
      Parameters.outerWidth P ≤ Parameters.balanceOrder P := by
  unfold Parameters.balanceOrder Parameters.outerWidth
  exact ⟨Nat.pow_le_pow_right (by norm_num) (firstExponent_le P),
    Nat.pow_le_pow_right (by norm_num) (outerExponent_le P)⟩

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- At every round level `i < k`, the widths of the physical parameters are below `n`. -/
theorem level_widths (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) (i : ℕ)
    (hi : i < ETHTailGrowth.repetitions c A d n) :
    2 * ETHTailGrowth.repetitions c A d n *
        EffectiveIteration.oneLevelBound (PhysicalLevelRun.physParameters G c
          (EffectiveIteration.sourceDepth n) (Iteration.seedState (EffectiveIteration.sourceDepth n)) i) < n ∧
    Parameters.balanceOrder (PhysicalLevelRun.physParameters G c
        (EffectiveIteration.sourceDepth n) (Iteration.seedState (EffectiveIteration.sourceDepth n)) i) < n ∧
    2 ^ Parameters.firstExponent (PhysicalLevelRun.physParameters G c
        (EffectiveIteration.sourceDepth n) (Iteration.seedState (EffectiveIteration.sourceDepth n)) i) < n ∧
    Parameters.outerWidth (PhysicalLevelRun.physParameters G c
        (EffectiveIteration.sourceDepth n) (Iteration.seedState (EffectiveIteration.sourceDepth n)) i) < n := by
  have hv : Fintype.card V ≤ 2 * Fintype.card E := hcommon.1
  have h := (CutoffBitMachine.actualClock_selected_levels G c A d n
    (ETHTailGrowth.repetitions c A d n) hv hlower hupper hrep (le_refl _) i hi).2
  rw [← PhysicalLevelRun.physParameters_eq] at h
  set P := PhysicalLevelRun.physParameters G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)) i with hP
  have hb := EffectiveIteration.balanceOrder_le_oneLevelBound P
  have hw := widths_le P
  have h1 : EffectiveIteration.oneLevelBound P ≤
      2 * ETHTailGrowth.repetitions c A d n * EffectiveIteration.oneLevelBound P :=
    Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨h, ?_, ?_, ?_⟩ <;> omega

#print axioms firstExponent_le
#print axioms outerExponent_le
#print axioms widths_le
#print axioms level_widths

end
end EthInapproximability.CurrentPaper.ClockG
