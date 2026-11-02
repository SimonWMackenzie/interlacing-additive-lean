import Paper2.E2Core
import Paper2.SelectedTapeAdapters

/-! a-eth-owner-2 copy of frozen `a-eth-owner-1/AEthClass.lean` (SHA-256 f15bf2137af723eedf944fb1fec2e007a5b46a19e938597bd89f7c1e1e670849). Changes: ONLY `EstimatesGrowingSel` and `estimatesGrowing_toPrefix` (verbatim, with the file header opens); every other declaration dropped (route A / square / prefix-carrier material not needed on route B). -/

noncomputable section

namespace Paper2.AEth

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.FiniteLaw
open Paper2.Unit4Shell.Definitions (uniformTape)
open Paper2.Unit4Shell.T10Finite
open Paper2.Unit4Shell.Asymptotics (kOf)

/-- **The estimator hypothesis of `thm:quantitative` in the R19 carrier**: a fixed-monomial
selected-tape algorithm (polynomial time and tape in the D-A3 matrix word, hence in `T`) that on
EVERY decodable matrix word `w` with target `D = d` prints, with probability `≥ 2/3`, a dyadic
value within `c·log₂ T / log₂ log₂ T` of `d` (`ADecider.accT`). -/
def EstimatesGrowingSel (E : SelectedTape.Algorithm) (c : ℝ) : Prop :=
  ∀ w (d : ℕ), AModel.targetD w = some d →
    2 / 3 ≤ E.prob w (fun out => ∃ v, AModel.decodeDyadic out = some v ∧
      |v - d| ≤ ADecider.accT c w)

theorem estimatesGrowing_toPrefix (E : SelectedTape.Algorithm) (c : ℝ)
    (h : EstimatesGrowingSel E c) : ADecider.EstimatesGrowing E.toPrefix c := by
  intro w d hd
  rw [SelectedTape.Algorithm.toPrefix_prob]
  exact h w d hd

end Paper2.AEth

end

#print axioms Paper2.AEth.estimatesGrowing_toPrefix
