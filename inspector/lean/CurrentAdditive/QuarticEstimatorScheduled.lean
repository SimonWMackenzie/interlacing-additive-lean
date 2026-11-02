import CurrentAdditive.QuarticEstimatorWords
import CurrentAdditive.QuarticEventuallyScheduled
import CurrentAdditive.QuarticEntryGrowth

noncomputable section

namespace Paper2.CurrentAdditive.QuarticConstructor

open _root_.CurrentAdditive.Eventual

open CurrentAdditive.QuarticSchedule
open CurrentAdditive.QuarticAsymptotics

theorem selected_rectangle_entries_eq_printed27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : Checks27 (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ) :
    (select27 hn edge Δ γ k).rows * (select27 hn edge Δ γ k).cols =
      _root_.CurrentAdditive.QuarticAsymptotics.printedT27 n m Δ γ k := by
  rw [select27_good hn edge Δ γ k hc]
  rfl

theorem selected_square_entries_eq_printed27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : Checks27 (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ) :
    SquarePadding.entries (select27 hn edge Δ γ k).rows
      (select27 hn edge Δ γ k).cols = printedTsq27 n m Δ γ k := by
  rw [select27_good hn edge Δ γ k hc]
  rfl

theorem matrixWord27_accuracy_scheduled {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : Checks27 (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (t : (select27 hn edge Δ γ k).Tape) (c : ℝ) :
    ADecider.accT c (matrixWord27 hn edge Δ γ k t) =
      c * (Real.logb 2 (_root_.CurrentAdditive.QuarticAsymptotics.printedT27 n m Δ γ k) /
        Real.logb 2 (Real.logb 2 (_root_.CurrentAdditive.QuarticAsymptotics.printedT27 n m Δ γ k))) := by
  rw [matrixWord27_accuracy]
  rw [selected_rectangle_entries_eq_printed27 hn edge Δ γ k hc]

theorem squareWord27_accuracy_scheduled {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : Checks27 (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (t : (select27 hn edge Δ γ k).Tape) (c : ℝ) :
    ADecider.accT c (squareWord27 hn edge Δ γ k t) =
      c * (Real.logb 2 (printedTsq27 n m Δ γ k) /
        Real.logb 2 (Real.logb 2 (printedTsq27 n m Δ γ k))) := by
  rw [squareWord27_accuracy]
  rw [selected_square_entries_eq_printed27 hn edge Δ γ k hc]

theorem matrixWord27_eventually_large (T₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ {n m : ℕ} (hn : 0 < n)
      (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ),
      2 ≤ n →
      Checks27 (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ →
      ∀ t : (select27 hn edge Δ γ (Unit4Shell.Asymptotics.kOf N)).Tape,
        T₀ ≤ entries (matrixWord27 hn edge Δ γ
          (Unit4Shell.Asymptotics.kOf N) t) := by
  obtain ⟨N₀, hN₀⟩ := generic_entries_eventually_ge T₀
  refine ⟨N₀, ?_⟩
  intro N hN n m hn edge Δ γ hn2 hc t
  rw [matrixWord27_entries, selected_rectangle_entries_eq_printed27 hn edge Δ γ _ hc]
  have hL : 1 ≤ Nat.clog 2 n :=
    Nat.succ_le_of_lt (Nat.clog_pos (by decide) (by omega))
  exact hN₀ N hN (Nat.clog 2 n)
    (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n))
    (CurrentAdditive.RandomizedSchedule.q27 (V := Fin n) (E := Fin m)
      (Nat.clog 2 n) γ Δ) hL

theorem squareWord27_eventually_large (T₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ {n m : ℕ} (hn : 0 < n)
      (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ),
      2 ≤ n →
      Checks27 (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ →
      ∀ t : (select27 hn edge Δ γ (Unit4Shell.Asymptotics.kOf N)).Tape,
        T₀ ≤ entries (squareWord27 hn edge Δ γ
          (Unit4Shell.Asymptotics.kOf N) t) := by
  obtain ⟨N₀, hN₀⟩ := matrixWord27_eventually_large T₀
  refine ⟨N₀, ?_⟩
  intro N hN n m hn edge Δ γ hn2 hc t
  have hr := hN₀ N hN hn edge Δ γ hn2 hc t
  rw [matrixWord27_entries] at hr
  rw [squareWord27_entries]
  exact hr.trans (Nat.mul_le_mul
    (SquarePadding.rows_le_side _ _) (SquarePadding.cols_le_side _ _))

#print axioms selected_rectangle_entries_eq_printed27
#print axioms selected_square_entries_eq_printed27
#print axioms matrixWord27_eventually_large
#print axioms squareWord27_eventually_large

end Paper2.CurrentAdditive.QuarticConstructor
