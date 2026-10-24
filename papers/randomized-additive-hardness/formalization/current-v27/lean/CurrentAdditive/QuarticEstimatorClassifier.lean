import CurrentAdditive.QuarticEstimatorPointwise

noncomputable section

namespace Paper2.CurrentAdditive.QuarticConstructor

open _root_.CurrentAdditive.Eventual

open Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper.EncodedCommunication (natField)
open Workspace.Types.CommComplexity

private theorem classify_one27 (E : SelectedTape.Algorithm) (w : List Bool)
    (d B k : ℕ) (a : ℝ)
    (hgap : 2 * a < k)
    (haccurate : 2 / 3 ≤ E.prob w (fun out => ∃ v,
      AModel.decodeDyadic out = some v ∧ |v - d| ≤ a)) :
    (d ≤ B →
      99 / 100 ≤ (HeaderStrip.selectedClassifier E).prob
        (natField (2 * B + k) ++ w) (· = [true])) ∧
    (B + k ≤ d →
      (HeaderStrip.selectedClassifier E).prob
        (natField (2 * B + k) ++ w) (· = [true]) ≤ 1 / 100) := by
  constructor
  · intro hd
    exact AEth.selectedClassifier_yes_at E a w d B k haccurate hgap hd
  · intro hd
    exact AEth.selectedClassifier_no_at E a w d B k haccurate hgap hd

/-- For every actual v27 rectangular word, the median classifier has the
claimed conditional YES and NO bias once the source is large. -/
theorem rectangular_classifier_at_large27 (E : SelectedTape.Algorithm) (c : ℝ)
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
        let o := select27 hn edge Δ γ (kOf N)
        (D (o.table t).matrix ≤ o.budget →
          99 / 100 ≤ (HeaderStrip.selectedClassifier E).prob
            (natField (2 * o.budget + kOf N) ++
              matrixWord27 hn edge Δ γ (kOf N) t) (· = [true])) ∧
        (o.budget + kOf N ≤ D (o.table t).matrix →
          (HeaderStrip.selectedClassifier E).prob
            (natField (2 * o.budget + kOf N) ++
              matrixWord27 hn edge Δ γ (kOf N) t) (· = [true]) ≤ 1 / 100) := by
  obtain ⟨N₀, hN₀⟩ := rectangular_estimator_at_large27 E c hc0 hc hE Δ p hΔ γ hγ
  refine ⟨N₀, ?_⟩
  intro N hN n m hn edge hincident hdegree hNm hmn hexp t
  dsimp only
  obtain ⟨hgap, hacc⟩ := hN₀ N hN hn edge hincident hdegree hNm hmn hexp t
  exact classify_one27 E (matrixWord27 hn edge Δ γ (kOf N) t)
    (D ((select27 hn edge Δ γ (kOf N)).table t).matrix)
    (select27 hn edge Δ γ (kOf N)).budget (kOf N)
    (ADecider.accT c (matrixWord27 hn edge Δ γ (kOf N) t)) hgap hacc

/-- The square-power-of-two version uses the same selected table and budget. -/
theorem square_classifier_at_large27 (E : SelectedTape.Algorithm) (c : ℝ)
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
        let o := select27 hn edge Δ γ (kOf N)
        (D (o.table t).matrix ≤ o.budget →
          99 / 100 ≤ (HeaderStrip.selectedClassifier E).prob
            (natField (2 * o.budget + kOf N) ++
              squareWord27 hn edge Δ γ (kOf N) t) (· = [true])) ∧
        (o.budget + kOf N ≤ D (o.table t).matrix →
          (HeaderStrip.selectedClassifier E).prob
            (natField (2 * o.budget + kOf N) ++
              squareWord27 hn edge Δ γ (kOf N) t) (· = [true]) ≤ 1 / 100) := by
  obtain ⟨N₀, hN₀⟩ := square_estimator_at_large27 E c hc0 hc hE Δ p hΔ γ hγ
  refine ⟨N₀, ?_⟩
  intro N hN n m hn edge hincident hdegree hNm hmn hexp t
  dsimp only
  obtain ⟨hgap, hacc⟩ := hN₀ N hN hn edge hincident hdegree hNm hmn hexp t
  exact classify_one27 E (squareWord27 hn edge Δ γ (kOf N) t)
    (D ((select27 hn edge Δ γ (kOf N)).table t).matrix)
    (select27 hn edge Δ γ (kOf N)).budget (kOf N)
    (ADecider.accT c (squareWord27 hn edge Δ γ (kOf N) t)) hgap hacc

#print axioms rectangular_classifier_at_large27
#print axioms square_classifier_at_large27

end Paper2.CurrentAdditive.QuarticConstructor
