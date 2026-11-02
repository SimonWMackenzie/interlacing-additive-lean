import CurrentAdditive.QuarticEstimatorScheduled
import Paper2.E2Classifier

noncomputable section

namespace Paper2.CurrentAdditive.QuarticConstructor

open _root_.CurrentAdditive.Eventual

open CurrentAdditive.QuarticAsymptotics
open Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper.EncodedCommunication (natField)

private theorem large_source_size27 {n m N Δ : ℕ} (γ : ℚ) (hΔ : 0 < Δ)
    (hN : Δ * max 2 (CurrentAdditive.QuarticSchedule.threshold27 Δ γ) ≤ N)
    (hNm : N ≤ m) (hmn : 2 * m ≤ Δ * n) :
    2 ≤ n ∧ CurrentAdditive.QuarticSchedule.threshold27 Δ γ ≤ n := by
  have hmul : Δ * max 2 (CurrentAdditive.QuarticSchedule.threshold27 Δ γ) ≤ Δ * n := by
    calc
      _ ≤ N := hN
      _ ≤ 2 * m := by omega
      _ ≤ Δ * n := hmn
  have hmax := Nat.le_of_mul_le_mul_left hmul hΔ
  exact ⟨(le_max_left _ _).trans hmax, (le_max_right _ _).trans hmax⟩

/-- On every tape of the literal v27 selector, an eventually accurate estimator
meets its promised error bound and that error is below half the chosen gap. -/
theorem rectangular_estimator_at_large27 (E : SelectedTape.Algorithm) (c : ℝ)
    (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hE : EstimatesGrowingEventuallySel E c)
    (Δ p : ℕ) (hΔ : 0 < Δ) (γ : ℚ) (hγ : 0 < γ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ {n m : ℕ} (hn : 0 < n)
      (edge : Fin m → Bool → Fin n),
      (∀ v, ∃ e b, edge e b = v) →
      (∀ v, SourceItems.degree edge v ≤ Δ) →
      N ≤ m → 2 * m ≤ Δ * n →
      n ≤ N * (Nat.clog 2 (N + 2)) ^ p →
      ∀ t : (select27 hn edge Δ γ (kOf N)).Tape,
        2 * ADecider.accT c (matrixWord27 hn edge Δ γ (kOf N) t) < kOf N ∧
        2 / 3 ≤ E.prob (matrixWord27 hn edge Δ γ (kOf N) t)
          (fun out => ∃ v, AModel.decodeDyadic out = some v ∧
            |v - Workspace.Types.CommComplexity.D
              ((select27 hn edge Δ γ (kOf N)).table t).matrix| ≤
              ADecider.accT c (matrixWord27 hn edge Δ γ (kOf N) t)) := by
  obtain ⟨T₀, hE⟩ := hE
  obtain ⟨Ngap, hgap⟩ := gap_exceeds_twice_error27 Δ γ hγ hΔ p c hc0 hc
  obtain ⟨Nentries, hentries⟩ := matrixWord27_eventually_large T₀
  refine ⟨max Ngap (max Nentries (Δ * max 2
    (CurrentAdditive.QuarticSchedule.threshold27 Δ γ))), ?_⟩
  intro N hN n m hn edge hincident hdegree hNm hmn hexp t
  have hNgap : Ngap ≤ N := (le_max_left _ _).trans hN
  have hNentries : Nentries ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNsize : Δ * max 2 (CurrentAdditive.QuarticSchedule.threshold27 Δ γ) ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨hn2, hsize⟩ := large_source_size27 γ hΔ hNsize hNm hmn
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hcheck := checks27_of_large hn edge Δ γ hγ hΔ hincident hdegree hsize
  have hgap' := hgap N hNgap n m edge hincident hdegree hNm hmn hexp
  constructor
  · rw [matrixWord27_accuracy_scheduled hn edge Δ γ (kOf N) hcheck t c]
    simpa only [mul_assoc] using hgap'
  · exact hE _ _ (matrixWord27_target hn edge Δ γ (kOf N) t)
      (hentries N hNentries hn edge Δ γ hn2 hcheck t)

/-- The same literal entry threshold and strict error margin after square
padding, with exactly preserved communication complexity. -/
theorem square_estimator_at_large27 (E : SelectedTape.Algorithm) (c : ℝ)
    (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hE : EstimatesGrowingEventuallySelSq E c)
    (Δ p : ℕ) (hΔ : 0 < Δ) (γ : ℚ) (hγ : 0 < γ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ {n m : ℕ} (hn : 0 < n)
      (edge : Fin m → Bool → Fin n),
      (∀ v, ∃ e b, edge e b = v) →
      (∀ v, SourceItems.degree edge v ≤ Δ) →
      N ≤ m → 2 * m ≤ Δ * n →
      n ≤ N * (Nat.clog 2 (N + 2)) ^ p →
      ∀ t : (select27 hn edge Δ γ (kOf N)).Tape,
        2 * ADecider.accT c (squareWord27 hn edge Δ γ (kOf N) t) < kOf N ∧
        2 / 3 ≤ E.prob (squareWord27 hn edge Δ γ (kOf N) t)
          (fun out => ∃ v, AModel.decodeDyadic out = some v ∧
            |v - Workspace.Types.CommComplexity.D
              ((select27 hn edge Δ γ (kOf N)).table t).matrix| ≤
              ADecider.accT c (squareWord27 hn edge Δ γ (kOf N) t)) := by
  obtain ⟨T₀, hE⟩ := hE
  obtain ⟨Ngap, hgap⟩ := gap_exceeds_twice_error_square27 Δ γ hγ hΔ p c hc0 hc
  obtain ⟨Nentries, hentries⟩ := squareWord27_eventually_large T₀
  refine ⟨max Ngap (max Nentries (Δ * max 2
    (CurrentAdditive.QuarticSchedule.threshold27 Δ γ))), ?_⟩
  intro N hN n m hn edge hincident hdegree hNm hmn hexp t
  have hNgap : Ngap ≤ N := (le_max_left _ _).trans hN
  have hNentries : Nentries ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNsize : Δ * max 2 (CurrentAdditive.QuarticSchedule.threshold27 Δ γ) ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨hn2, hsize⟩ := large_source_size27 γ hΔ hNsize hNm hmn
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hcheck := checks27_of_large hn edge Δ γ hγ hΔ hincident hdegree hsize
  have hgap' := hgap N hNgap n m edge hincident hdegree hNm hmn hexp
  constructor
  · rw [squareWord27_accuracy_scheduled hn edge Δ γ (kOf N) hcheck t c]
    simpa only [mul_assoc] using hgap'
  · exact hE _ _ (squareWord27_target hn edge Δ γ (kOf N) t)
      (squareWord27_square hn edge Δ γ (kOf N) t)
      (hentries N hNentries hn edge Δ γ hn2 hcheck t)

#print axioms rectangular_estimator_at_large27
#print axioms square_estimator_at_large27

end Paper2.CurrentAdditive.QuarticConstructor
