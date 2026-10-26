import CurrentAdditive.QuarticUniformInputCap
import CurrentAdditive.QuarticClockArithmetic

/-! Isolate the literal numeric input-cap computation from physical machines. -/

namespace Paper2.CurrentAdditive.QuarticInputCapAtoms

open EthInapproximability.CurrentPaper
open Paper2.CurrentAdditive.QuarticClockArithmetic
open Paper2.CurrentAdditive.QuarticTMClockRepair

noncomputable section

theorem input_cap_formula
    (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ) (k L : ℕ) :
    QuarticUniformInputCap.inputCap g Δ γ k L =
      4 + 2 * ((EncodedGraph.encode g).length + k + L) +
      rawCoefficient Δ γ *
        ((g.vertices + 2) ^ (rawExponent Δ γ * (k + 1)) + L) := by
  rfl

#print axioms input_cap_formula

end
end Paper2.CurrentAdditive.QuarticInputCapAtoms
