import CurrentAdditive.V42PublicSchedule
import CurrentAdditive.V39BudgetPrintedLaw

/-! Source v42 thm:compression and its literal single final sample count.
The rank-generated compatible catalogue is proved in the imported counting
theorem. No successful-sampling event or sampling certificate is a premise. -/

namespace CurrentAdditive.V42Compression
noncomputable section

open Paper2 Workspace.Types.CommComplexity V42PublicSchedule

theorem sampleSide_eq (L K : ℕ) :
    sampleSide L K=V38RankCount.squareDrawsV38 (rankBound L K) (H L K) := by
  unfold sampleSide V38Schedule.pow2Ceil V38RankCount.squareDrawsV38 V38RankCount.leafBitsV38
  congr 2
  ring

theorem sampleSide_pos (L K : ℕ) : 0 < sampleSide L K :=
  (by positivity : 0 < 2^(H L K)).trans_le (sampleSide_lower L K)

theorem H_pos (L K : ℕ) : 1 ≤ H L K := by
  have hh:=B_ge_seven L K
  unfold H
  omega

theorem ideal_failure {X Y : Type*} [Fintype X] [Fintype Y]
    (L K : ℕ) (F : X → Y → Bool)
    (μX : PositiveRationalLaw X) (μY : PositiveRationalLaw Y)
    (hrank : (RankLeaves.realMatrix F).rank ≤ rankBound L K)
    (hrobust : ∀ U V, (3/5:ℝ) ≤ μX.toFiniteLaw.prob (· ∈ U) →
      (3/5:ℝ) ≤ μY.toFiniteLaw.prob (· ∈ V) →
      H L K ≤ Compression.restrictionD F U V) :
    ((μX.iid (sampleSide L K)).prod (μY.iid (sampleSide L K))).toFiniteLaw.prob
      (fun z => D (sampleMatrix F z.1 z.2) < H L K) < (1:ℝ)/100 := by
  rw [sampleSide_eq]
  exact V39BudgetPrintedLaw.row_first_compression F μX μY
    (rankBound L K) (H L K) (H_pos L K) hrank hrobust

theorem sample_upper {X Y : Type*} [Fintype X] [Fintype Y] (L K : ℕ) (F : X → Y → Bool)
    (xs : Fin (sampleSide L K) → X) (ys : Fin (sampleSide L K) → Y) :
    D (sampleMatrix F xs ys) ≤ D F :=
  Workspace.ProofLemmas.SublemmaPrecompNoIncrease F xs ys

theorem ideal_exact {X Y : Type*} [Fintype X] [Fintype Y]
    (L K : ℕ) (F : X → Y → Bool)
    (μX : PositiveRationalLaw X) (μY : PositiveRationalLaw Y)
    (hrank : (RankLeaves.realMatrix F).rank ≤ rankBound L K)
    (hupper : D F ≤ H L K)
    (hrobust : ∀ U V, (3/5:ℝ) ≤ μX.toFiniteLaw.prob (· ∈ U) →
      (3/5:ℝ) ≤ μY.toFiniteLaw.prob (· ∈ V) →
      H L K ≤ Compression.restrictionD F U V) :
    (99/100:ℝ) <
      ((μX.iid (sampleSide L K)).prod (μY.iid (sampleSide L K))).toFiniteLaw.prob
        (fun z => D (sampleMatrix F z.1 z.2)=H L K) := by
  have hf:=ideal_failure L K F μX μY hrank hrobust
  have he : (fun z : (Fin (sampleSide L K) → X) × (Fin (sampleSide L K) → Y) =>
      D (sampleMatrix F z.1 z.2)=H L K)=
      (fun z => ¬D (sampleMatrix F z.1 z.2)<H L K) := by
    funext z
    have hu:=(sample_upper L K F z.1 z.2).trans hupper
    apply propext
    omega
  rw [he,V39BudgetPrintedLaw.prob_not]
  linarith

#print axioms ideal_failure
#print axioms ideal_exact

end
end CurrentAdditive.V42Compression
