import Paper2.E2Classifier
import Paper2.E2Gap

/-! a-eth-owner-2 copy of frozen `a-eth-owner-1/AEthPerTape.lean` (SHA-256 8d3dcea0cabc19229f9055936d6c585e3ebab583c9189a323f0020a6a2d6f254). Changes: imports `AEthClassifier`, `AEthGap` -> `E2Classifier`, `E2Gap`. -/

/-!
# Paper A (lock v12), lane `owner:a-eth-1`, segment 3 (partial): per-reduction-tape classifier
bounds for the growing-gap decider

Lock v12 `sections/06-reduction.tex:134-137`: "Thus for every fixed $c<1/12$ the gap $k$
eventually exceeds twice the proposed error. The midpoint test from \cref{intro:corollary}
decides the formula with bounded error."

`classifier_per_tape`: for every density `cs`, `0 ≤ c < 1/12` there is `N₀` such that for every
sparse valid `Φ` with `N ≥ N₀`, every growing selected estimator `E` and EVERY reduction tape `b`
at `k = kOf N`, the admitted (A27) selected classifier run on the headered printed word
`natField (2·budget + k) ++ mwOf b` accepts with probability `≥ 99/100` when `D(table b) ≤ budget`
and `≤ 1/100` when `budget + k ≤ D(table b)`. Combined with the admitted T01 law (`t01_yes`: every
tape is `≤ budget` on YES; `t01_no`: `Pr[D ≥ budget + k] ≥ 981/1000` on NO) this is the
per-tape half of the error analysis of a "reduction, then header, then classifier" decider
(route B, the T02 `HeaderClassifierJoin` pattern); the join law itself is NOT proved here.

No ledger row is closed.
-/

noncomputable section

namespace Paper2.AEth

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open EthInapproximability.CurrentPaper.EncodedCommunication (natField)
open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

set_option hygiene false in
local notation "EXP" Φ:max k:max => TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
  (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k

/-- The headered printed word at reduction tape `b`. -/
def headerWord (Φ : ValidFormula) (k : ℕ) (b : (EXP Φ k).output.Tape) : List Bool :=
  natField (2 * (EXP Φ k).output.budget + k) ++ ADecider.mwOf D B Φ k b

/-- **Per-tape classifier bounds at the growing gap.** -/
theorem classifier_per_tape (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables → ∀ E : SelectedTape.Algorithm, EstimatesGrowingSel E c →
      ∀ b : (EXP Φ (kOf Φ.val.variables)).output.Tape,
      (Workspace.Types.CommComplexity.D
          ((EXP Φ (kOf Φ.val.variables)).output.table b).matrix ≤
          (EXP Φ (kOf Φ.val.variables)).output.budget →
        99 / 100 ≤ (Paper2.HeaderStrip.selectedClassifier E).prob
          (headerWord D B Φ (kOf Φ.val.variables) b) (· = [true])) ∧
      ((EXP Φ (kOf Φ.val.variables)).output.budget + kOf Φ.val.variables ≤
          Workspace.Types.CommComplexity.D
            ((EXP Φ (kOf Φ.val.variables)).output.table b).matrix →
        (Paper2.HeaderStrip.selectedClassifier E).prob
          (headerWord D B Φ (kOf Φ.val.variables) b) (· = [true]) ≤ 1 / 100) := by
  obtain ⟨N₀, hN₀⟩ := gap_at_mw D B cs c hc0 hc
  refine ⟨N₀, fun Φ hsp hN E hE b => ?_⟩
  have hgap := hN₀ Φ hsp hN b
  have htarget := ADecider.targetD_mwOf D B Φ (kOf Φ.val.variables) b
  have hk : 2 * ADecider.accT c (ADecider.mwOf D B Φ (kOf Φ.val.variables) b) <
      ((kOf Φ.val.variables : ℕ) : ℝ) := hgap
  exact ⟨fun hle => growing_classifier_yes E c hE _ _ _ _ htarget hk hle,
    fun hge => growing_classifier_no E c hE _ _ _ _ htarget hk hge⟩

end Paper2.AEth

end

#print axioms Paper2.AEth.classifier_per_tape
