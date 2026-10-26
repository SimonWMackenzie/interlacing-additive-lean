import CurrentAdditive.QuarticSparseBridge

/-! The final R20 contradiction once the one physical v27 algorithm is
constructed for each sparse density. -/

noncomputable section

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.AEth2
open _root_.CurrentAdditive.Eventual
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition

theorem no_randomized_sparse_ETH_of_joint_runtime27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (E : SelectedTape.Algorithm) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : c < 1 / 12) (hE : EstimatesGrowingEventuallySelSq E c)
    (hphysical : ∀ cs : ℕ, ∃ N₁ : ℕ,
      ∃ hcut : cutN27 Dsrc Bsrc E c hc0 hc hE cs ≤ N₁,
      ∃ A : ETape.Algorithm,
      (∀ x : List Bool,
        JoinRealisesSqAt27 Dsrc Bsrc x
          (Paper2.AEth4.routedV (cs + 2) N₁
            ((cutN27_pos Dsrc Bsrc E c hc0 hc hE cs).trans hcut) x) E A) ∧
      (∀ ε : ℝ, 0 < ε → ∃ C d N₀ : ℕ,
        ∀ input, Paper2.AModel.WellFormedCNF input →
        Paper2.AModel.cnfClauseCount input ≤
          cs * EncodedETHTail.variableCount input →
        N₀ ≤ EncodedETHTail.variableCount input →
        A.time input ≤ C *
          ⌈(2 : ℝ) ^ (ε * EncodedETHTail.variableCount input)⌉₊ *
          (input.length + 1) ^ d)) :
    ¬ RandomizedSparseETH_R20 := by
  apply not_R20_iff.mpr
  intro cs
  obtain ⟨N₁, hcut, A, hJ, hT⟩ := hphysical cs
  exact ⟨A, sparse_of_joint_runtime_at27 Dsrc Bsrc E c hc0 hc hE
    cs N₁ hcut A hJ hT⟩

#print axioms no_randomized_sparse_ETH_of_joint_runtime27

end Paper2.CurrentAdditive.QuarticClassEndpoint

end
