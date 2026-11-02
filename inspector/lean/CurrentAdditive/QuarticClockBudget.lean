import CurrentAdditive.QuarticClockPoly
import Paper2.E6Clock

/-! Once each physical stage fits the common source-size parameter, the
entire v27 decision clock meets the R20 sparse running-time budget. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.AEth4

theorem decisionEnvelope_budget27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (C : Paper2.SelectedTape.Algorithm) (cs J : ℕ)
    (T : ValidFormula → ℕ) (N₂ : ℕ)
    (hT : ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₂ ≤ Φ.val.variables →
      let Y := ((EncodedCNF.encode Φ.val).length + 1) *
        (Paper2.AEth.expLen Φ.val.variables + 1) *
        ((t10Graph Dsrc Bsrc Φ).vertices + 2) ^
          (J * (kOf Φ.val.variables + 1))
      T Φ ≤ 5000 * (Y + 1) + Paper2.AEth5.clsTime C Y Y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C' d N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      T Φ ≤ C' * ⌈(2 : ℝ) ^ (ε * Φ.val.variables)⌉₊ *
        ((EncodedCNF.encode Φ.val).length + 1) ^ d := by
  exact budget_of_dom Dsrc Bsrc cs J T
    (fun Z => 5000 * (Z + 1) + Paper2.AEth5.clsTime C Z Z)
    (decisionEnvelope_poly27 C) N₂ hT ε hε

#print axioms decisionEnvelope_budget27

end Paper2.CurrentAdditive.QuarticClassEndpoint
