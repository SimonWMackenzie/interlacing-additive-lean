import CurrentAdditive.EventualEmission
import Paper2.E2Sq

/-! Private per-tape classifier statements using the literal sufficiently-large
table-entry hypothesis. No production theorem is modified. -/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 1024

namespace CurrentAdditive.Eventual

open Paper2

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

set_option hygiene false in
local notation "EXP" Φ:max k:max => TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
  (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k

/-- Rectangular per-reduction-tape bounds, with accuracy only on sufficiently
large decoded tables. The source cutoff absorbs the estimator's unknown but
fixed threshold. -/
theorem classifier_per_tape_eventual (cs : ℕ) (c : ℝ)
    (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (E : SelectedTape.Algorithm) (hE : EstimatesGrowingEventuallySel E c) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      ∀ b : (EXP Φ (kOf Φ.val.variables)).output.Tape,
      (Workspace.Types.CommComplexity.D
          ((EXP Φ (kOf Φ.val.variables)).output.table b).matrix ≤
          (EXP Φ (kOf Φ.val.variables)).output.budget →
        99 / 100 ≤ (Paper2.HeaderStrip.selectedClassifier E).prob
          (AEth.headerWord D B Φ (kOf Φ.val.variables) b) (· = [true])) ∧
      ((EXP Φ (kOf Φ.val.variables)).output.budget + kOf Φ.val.variables ≤
          Workspace.Types.CommComplexity.D
            ((EXP Φ (kOf Φ.val.variables)).output.table b).matrix →
        (Paper2.HeaderStrip.selectedClassifier E).prob
          (AEth.headerWord D B Φ (kOf Φ.val.variables) b) (· = [true]) ≤ 1 / 100) := by
  obtain ⟨T₀, hE⟩ := hE
  obtain ⟨N₁, hgap⟩ := AEth.gap_at_mw D B cs c hc0 hc
  obtain ⟨N₂, hentries⟩ := emitted_entries_eventually_ge D B T₀
  refine ⟨max N₁ N₂, ?_⟩
  intro Φ hsp hN b
  have hN₁ : N₁ ≤ Φ.val.variables := (le_max_left _ _).trans hN
  have hN₂ : N₂ ≤ Φ.val.variables := (le_max_right _ _).trans hN
  have hd := ADecider.targetD_mwOf D B Φ (kOf Φ.val.variables) b
  have ha := hE _ _ hd (hentries Φ hN₂ b)
  have hk := hgap Φ hsp hN₁ b
  constructor
  · intro hle
    exact AEth.selectedClassifier_yes_at E _ _ _ _ _ ha hk hle
  · intro hge
    exact AEth.selectedClassifier_no_at E _ _ _ _ _ ha hk hge

/-- Square power-of-two variant, with the threshold applied to the padded
table's actual entry count. -/
theorem classifier_per_tape_square_eventual (cs : ℕ) (c : ℝ)
    (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (E : SelectedTape.Algorithm) (hE : EstimatesGrowingEventuallySelSq E c) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      ∀ b : (EXP Φ (kOf Φ.val.variables)).output.Tape,
      (Workspace.Types.CommComplexity.D
          ((EXP Φ (kOf Φ.val.variables)).output.table b).matrix ≤
          (EXP Φ (kOf Φ.val.variables)).output.budget →
        99 / 100 ≤ (Paper2.HeaderStrip.selectedClassifier E).prob
          (AEth2.headerWordSq D B Φ (kOf Φ.val.variables) b) (· = [true])) ∧
      ((EXP Φ (kOf Φ.val.variables)).output.budget + kOf Φ.val.variables ≤
          Workspace.Types.CommComplexity.D
            ((EXP Φ (kOf Φ.val.variables)).output.table b).matrix →
        (Paper2.HeaderStrip.selectedClassifier E).prob
          (AEth2.headerWordSq D B Φ (kOf Φ.val.variables) b) (· = [true]) ≤ 1 / 100) := by
  obtain ⟨T₀, hE⟩ := hE
  obtain ⟨N₁, hgap⟩ := AEth2.gap_at_mwSq D B cs c hc0 hc
  obtain ⟨N₂, hentries⟩ := emitted_square_entries_eventually_ge D B T₀
  refine ⟨max N₁ N₂, ?_⟩
  intro Φ hsp hN b
  have hN₁ : N₁ ≤ Φ.val.variables := (le_max_left _ _).trans hN
  have hN₂ : N₂ ≤ Φ.val.variables := (le_max_right _ _).trans hN
  have hd := ADecider.targetD_mwSqOf D B Φ (kOf Φ.val.variables) b
  have hsq := ADecider.squareWord_mwSqOf D B Φ (kOf Φ.val.variables) b
  have ha := hE _ _ hd hsq (hentries Φ hN₂ b)
  have hk := hgap Φ hsp hN₁ b
  constructor
  · intro hle
    exact AEth.selectedClassifier_yes_at E _ _ _ _ _ ha hk hle
  · intro hge
    exact AEth.selectedClassifier_no_at E _ _ _ _ _ ha hk hge

#print axioms classifier_per_tape_eventual
#print axioms classifier_per_tape_square_eventual

end CurrentAdditive.Eventual
