import CurrentAdditive.QuarticSquareLengthPoly

/-! A numeric source-size cap that avoids elaborating the selected tape type. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition

theorem source_graph_power_fit27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (cs J : ℕ) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      ((t10Graph Dsrc Bsrc Φ).vertices + 2) ^
        (J * (kOf Φ.val.variables + 1)) ≤
        Paper2.AEth.expLen Φ.val.variables := by
  obtain ⟨N₁, hN₁⟩ := Paper2.AEth3.bits_fit J (Dsrc.sizeExponent + 2)
  refine ⟨max N₁
    (2 ^ (2 ^ (Dsrc.sizeExponent + 1) *
      Paper2.Unit4Shell.T10Size.t45C Dsrc Bsrc cs)), ?_⟩
  intro Φ hsp hN
  have h1 : N₁ ≤ Φ.val.variables := (le_max_left _ _).trans hN
  have h4 : 2 ^ (2 ^ (Dsrc.sizeExponent + 1) *
      Paper2.Unit4Shell.T10Size.t45C Dsrc Bsrc cs) ≤ Φ.val.variables :=
    (le_max_right _ _).trans hN
  have hsize := Paper2.Unit4Shell.T10Size.t45_shell_form
    Dsrc Bsrc cs Φ hsp h4
  exact hN₁ Φ.val.variables h1 _ hsize

#print axioms source_graph_power_fit27

end Paper2.CurrentAdditive.QuarticClassEndpoint
