import CurrentAdditive.QuarticUniformDecisionClock
import CurrentAdditive.QuarticClockBudget

/-! A fixed multiplicative slack in the common source-size cap preserves D-A6. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.AEth4
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem decisionEnvelope_scaled_poly27
    (C : Paper2.SelectedTape.Algorithm) (A : ℕ) :
    Paper2.Unit4Shell.Poly.PolyIn id
      (fun Z => 5000 * (A * (Z + 1) + 1) +
        Paper2.AEth5.clsTime C (A * (Z + 1)) (A * (Z + 1))) := by
  unfold Paper2.AEth5.clsTime NPOwner1.Trunc.timeBound
  repeat (first
    | exact Paper2.Unit4Shell.Poly.self
    | exact Paper2.Unit4Shell.Poly.const _
    | apply Paper2.Unit4Shell.Poly.add
    | apply Paper2.Unit4Shell.Poly.mul
    | apply Paper2.Unit4Shell.Poly.pow)

theorem decisionEnvelope_scaled_budget27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (C : Paper2.SelectedTape.Algorithm) (cs J A : ℕ)
    (T : ValidFormula → ℕ) (N₂ : ℕ)
    (hT : ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₂ ≤ Φ.val.variables →
      let Y := ((EncodedCNF.encode Φ.val).length + 1) *
        (Paper2.AEth.expLen Φ.val.variables + 1) *
        ((t10Graph Dsrc Bsrc Φ).vertices + 2) ^
          (J * (kOf Φ.val.variables + 1))
      T Φ ≤ 5000 * (A * (Y + 1) + 1) +
        Paper2.AEth5.clsTime C (A * (Y + 1)) (A * (Y + 1)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C' d N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      T Φ ≤ C' * ⌈(2 : ℝ) ^ (ε * Φ.val.variables)⌉₊ *
        ((EncodedCNF.encode Φ.val).length + 1) ^ d := by
  exact budget_of_dom Dsrc Bsrc cs J T
    (fun Z => 5000 * (A * (Z + 1) + 1) +
      Paper2.AEth5.clsTime C (A * (Z + 1)) (A * (Z + 1)))
    (decisionEnvelope_scaled_poly27 C A) N₂ hT ε hε

#print axioms decisionEnvelope_scaled_poly27
#print axioms decisionEnvelope_scaled_budget27

end Paper2.CurrentAdditive.QuarticClassEndpoint
