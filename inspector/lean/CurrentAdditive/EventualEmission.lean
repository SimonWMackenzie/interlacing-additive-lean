import CurrentAdditive.EventualDomain
import Paper2.E2PerTape
import Paper2.AEndpoint

/-! Private bridge: the estimator sees the actual scheduled matrix word,
whose decoded number of entries eventually passes an arbitrary fixed cutoff.
The old production sources are unchanged. -/

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
local notation "SEL" Φ:max k:max => TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
  (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k

set_option hygiene false in
local notation "EXP" Φ:max k:max => TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
  (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k

theorem vertices_two_of_large (Φ : ValidFormula)
    (hN : B.degreeBound + 1 ≤ Φ.val.variables) :
    2 ≤ (t10Graph D B Φ).vertices := by
  obtain ⟨hNm, hmn, _⟩ := Unit4Shell.T10Size.t45_relations D B Φ
  have hnpos := t10_vertices_pos D B Φ
  by_contra h
  have hn1 : (t10Graph D B Φ).vertices = 1 := by omega
  simp only [hn1, mul_one] at hmn
  omega

theorem entries_mwOf_eq_printed (Φ : ValidFormula) (k : ℕ)
    (hsize : CompletePublicScheduleScratch.sizeThreshold B.degreeBound (sourceGap D B) ≤
      (t10Graph D B Φ).vertices)
    (b : (EXP Φ k).output.Tape) :
    entries (ADecider.mwOf D B Φ k b) =
      printedT (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length
        B.degreeBound (sourceGap D B) k := by
  have hm : entries (ADecider.mwOf D B Φ k b) =
      (EXP Φ k).output.rows * (EXP Φ k).output.cols := by
    unfold ADecider.mwOf
    exact entries_matrixWord _ _ _ (ADecider.mwOf_valid D B Φ k b)
  rw [hm, TotalFiniteConstructorScratch.experiment_output_eq_select]
  exact (AEndpoint.entries_eq_printed D B Φ k hsize).1

theorem entries_mwSqOf_eq_printed (Φ : ValidFormula) (k : ℕ)
    (hsize : CompletePublicScheduleScratch.sizeThreshold B.degreeBound (sourceGap D B) ≤
      (t10Graph D B Φ).vertices)
    (b : (EXP Φ k).output.Tape) :
    entries (ADecider.mwSqOf D B Φ k b) =
      printedTsq (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length
        B.degreeBound (sourceGap D B) k := by
  have hm : entries (ADecider.mwSqOf D B Φ k b) =
      SquarePadding.entries (EXP Φ k).output.rows (EXP Φ k).output.cols := by
    unfold ADecider.mwSqOf
    exact entries_matrixWord _ _ _ (ADecider.mwSqOf_valid D B Φ k b)
  rw [hm, TotalFiniteConstructorScratch.experiment_output_eq_select]
  exact (AEndpoint.entries_eq_printed D B Φ k hsize).2

theorem emitted_entries_eventually_ge (T₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula, N₀ ≤ Φ.val.variables →
      ∀ b : (EXP Φ (kOf Φ.val.variables)).output.Tape,
        T₀ ≤ entries (ADecider.mwOf D B Φ (kOf Φ.val.variables) b) := by
  obtain ⟨N₁, hN₁⟩ := printedT_eventually_ge T₀
  refine ⟨max N₁ (max (B.degreeBound + 1)
    (B.degreeBound * CompletePublicScheduleScratch.sizeThreshold
      B.degreeBound (sourceGap D B))), ?_⟩
  intro Φ hN b
  have hN₁small : N₁ ≤ Φ.val.variables := (le_max_left _ _).trans hN
  have htwo : 2 ≤ (t10Graph D B Φ).vertices :=
    vertices_two_of_large D B Φ ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hsize := AEndpoint.size_of_large D B Φ
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  rw [entries_mwOf_eq_printed D B Φ _ hsize b]
  exact hN₁ Φ.val.variables hN₁small _ _ _ _ htwo

theorem emitted_square_entries_eventually_ge (T₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula, N₀ ≤ Φ.val.variables →
      ∀ b : (EXP Φ (kOf Φ.val.variables)).output.Tape,
        T₀ ≤ entries (ADecider.mwSqOf D B Φ (kOf Φ.val.variables) b) := by
  obtain ⟨N₁, hN₁⟩ := printedTsq_eventually_ge T₀
  refine ⟨max N₁ (max (B.degreeBound + 1)
    (B.degreeBound * CompletePublicScheduleScratch.sizeThreshold
      B.degreeBound (sourceGap D B))), ?_⟩
  intro Φ hN b
  have hN₁small : N₁ ≤ Φ.val.variables := (le_max_left _ _).trans hN
  have htwo : 2 ≤ (t10Graph D B Φ).vertices :=
    vertices_two_of_large D B Φ ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hsize := AEndpoint.size_of_large D B Φ
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  rw [entries_mwSqOf_eq_printed D B Φ _ hsize b]
  exact hN₁ Φ.val.variables hN₁small _ _ _ _ htwo

#print axioms vertices_two_of_large
#print axioms entries_mwOf_eq_printed
#print axioms emitted_entries_eventually_ge
#print axioms entries_mwSqOf_eq_printed
#print axioms emitted_square_entries_eventually_ge

end CurrentAdditive.Eventual
