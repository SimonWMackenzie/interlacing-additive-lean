import CurrentAdditive.DeterministicETHSourceBridge

/-! The NO promise for the exact T10 graph is the quantified monochromatic-
edge lower bound, not the absence of a YES witness supplied to a constructor. -/

namespace CurrentAdditive.DeterministicETHGapNo

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2
open Paper2.Unit4Shell.T10Finite

def GapNo {v e : ℕ} (γ : ℚ) (G : Fin e → Bool → Fin v) : Prop :=
  ∀ colour : Fin v → Fin 3,
    (γ : ℝ) * e ≤
      ((Finset.univ.filter (fun z =>
        colour (G z false) = colour (G z true))).card : ℝ)

theorem t10_no_gap
    (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
    (Φ : ValidFormula) (hno : ¬ EncodedCNF.Satisfiable Φ.val) :
    GapNo (sourceGap D B)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
        (t10Graph_valid D B Φ)) := by
  exact (t10_source D B Φ).2.2.2.2.2.2 hno

theorem gap_no_excludes_three_colourable {v e : ℕ}
    (γ : ℚ) (G : Fin e → Bool → Fin v)
    (hγ : 0 < γ) (he : 0 < e) (hno : GapNo γ G) :
    ¬ Paper2.FiniteFallbackOutput.ThreeColourable G := by
  rintro ⟨colour, proper⟩
  have hzero : (Finset.univ.filter (fun z : Fin e =>
      colour (G z false) = colour (G z true))).card = 0 := by
    have heq : Finset.univ.filter (fun z : Fin e =>
        colour (G z false) = colour (G z true)) = ∅ := by
      ext z
      simp [proper z]
    simp [heq]
  have hbound := hno colour
  rw [hzero] at hbound
  have hγreal : (0 : ℝ) < (γ : ℝ) := by exact_mod_cast hγ
  have hereal : (0 : ℝ) < e := by exact_mod_cast he
  have hb : (γ : ℝ) * e ≤ 0 := by simpa using hbound
  exact (not_le_of_gt (mul_pos hγreal hereal)) hb

#print axioms t10_no_gap
#print axioms gap_no_excludes_three_colourable

end CurrentAdditive.DeterministicETHGapNo
