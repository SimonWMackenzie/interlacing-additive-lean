import Paper2.E2Core
import Paper2.A4ShellsTight

/-! a-eth-owner-2 copy of frozen `a-eth-owner-1/AEthGap.lean` (SHA-256 e66774899f2394325b67c831381c851ea4471c58da2b5fb6df4b61706ece340c). Changes: import `AEthDT24` -> `E2Core`. -/

/-!
# Paper A (lock v12), lane `owner:a-eth-1`, segment 3 (partial): the growing gap exceeds twice the
per-word accuracy at EVERY printed matrix word

Lock v12 `sections/06-reduction.tex:134-135`: "Thus for every fixed $c<1/12$ the gap $k$
eventually exceeds twice the proposed error."

`gap_at_mw`: for every density `cs` and `0 ≤ c < 1/12` there is `N₀` such that for every sparse
valid `Φ` with `N ≥ N₀` and EVERY reduction tape `b` at `k = kOf N`,
`2 · accT c (mwOf b) < kOf N`, where `accT c w = c·log₂T/log₂log₂T` is the growing accuracy at
the printed matrix word. This is the per-word hypothesis `hk` of
`AEthClassifier.growing_classifier_yes/no`. Wiring copied from the admitted
`ShellsTight.T24_source_shell` (same admitted source facts), applied to the admitted
`Asymptotics.gap_exceeds_twice_error`; the printed-dimension identity is the admitted
`HA3Endpoints.T24_final` component (as in `ADecider.decider_error`).

No ledger row is closed.
-/

noncomputable section

namespace Paper2.AEth

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

set_option hygiene false in
local notation "EXP" Φ:max k:max => TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
  (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k

/-- **The growing gap exceeds twice the accuracy at every printed matrix word.** -/
theorem gap_at_mw (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables → ∀ b : (EXP Φ (kOf Φ.val.variables)).output.Tape,
      2 * ADecider.accT c (ADecider.mwOf D B Φ (kOf Φ.val.variables) b) <
        (kOf Φ.val.variables : ℝ) := by
  obtain ⟨N₁, hN₁⟩ := gap_exceeds_twice_error B.degreeBound (sourceGap D B)
    (source_gap_pos D B) (by have := B.degreeBound_pos; omega) (D.sizeExponent + 2)
    c hc0 hc
  obtain ⟨M, hM⟩ := A3CloseEndpoints.T24_final D B EncodedCNF.Language AEndpoint.DA2_recommended
    cs c hc0 hc false
  obtain ⟨N₂, hN₂⟩ := hM 1 one_pos
  refine ⟨max (max N₁ N₂) (2 ^ (2 ^ (D.sizeExponent + 1) * Paper2.Unit4Shell.T10Size.t45C D B cs)),
    ?_⟩
  intro Φ hsp hN b
  have h1 : N₁ ≤ Φ.val.variables := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have h2 : N₂ ≤ Φ.val.variables := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have h4 : 2 ^ (2 ^ (D.sizeExponent + 1) * Paper2.Unit4Shell.T10Size.t45C D B cs) ≤
      Φ.val.variables := le_trans (le_max_right _ _) hN
  haveI : NeZero (t10Graph D B Φ).vertices := ⟨(t10_vertices_pos D B Φ).ne'⟩
  obtain ⟨_, _, hinc, hdeg, _, _, _⟩ := t10_source D B Φ
  obtain ⟨hNm, hmn, _⟩ := Paper2.Unit4Shell.T10Size.t45_relations D B Φ
  have hsize := Paper2.Unit4Shell.T10Size.t45_shell_form D B cs Φ hsp h4
  have hgap := hN₁ Φ.val.variables h1 _ _
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) hinc hdeg hNm hmn hsize
  obtain ⟨_, _, _, hdims, _, _⟩ := hN₂ Φ hsp h2
  have hdimsE : (EXP Φ (kOf Φ.val.variables)).output.rows *
      (EXP Φ (kOf Φ.val.variables)).output.cols =
      printedT (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length B.degreeBound
        (sourceGap D B) (kOf Φ.val.variables) := by
    rw [TotalFiniteConstructorScratch.experiment_output_eq_select]; exact hdims
  rw [ADecider.accT_mwOf, hdimsE]
  linarith [hgap]

end Paper2.AEth

end

#print axioms Paper2.AEth.gap_at_mw
