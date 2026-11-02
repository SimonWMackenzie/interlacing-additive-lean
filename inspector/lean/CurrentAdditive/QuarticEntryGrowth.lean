import CurrentAdditive.EventualDomain
import CurrentAdditive.RandomizedSchedule

/-! Dimension-only v27 transfer for the eventual table-entry threshold.
This does not construct a v27 reduction or assert any run-success law. -/

noncomputable section

namespace Paper2.CurrentAdditive

open _root_.CurrentAdditive.Eventual

open Paper2.SourceRecursiveNoSampling
open Paper2.Unit4Shell.Asymptotics
open Paper2.SourceProfileParameters
open Paper2.RestorationWidthScheduleScratch

variable {V Edges : Type*} [Fintype V] [Nonempty V] [Fintype Edges]

def printedRows27 (L Δ : ℕ) (γ : ℚ) (k : ℕ) : ℕ :=
  sourceRows L (4 * ell L)
    (CurrentAdditive.RandomizedSchedule.q27 (V := V) (E := Edges) L γ Δ) k

def printedCols27 (L Δ : ℕ) (γ : ℚ) (k : ℕ) : ℕ :=
  sourceCols L (4 * ell L)
    (CurrentAdditive.RandomizedSchedule.q27 (V := V) (E := Edges) L γ Δ) k

def printedT27 (L Δ : ℕ) (γ : ℚ) (k : ℕ) : ℕ :=
  printedRows27 (V := V) (Edges := Edges) L Δ γ k *
    printedCols27 (V := V) (Edges := Edges) L Δ γ k

omit [Nonempty V] in
theorem printedT27_eventually_ge (T₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ L Δ : ℕ, ∀ γ : ℚ, 1 ≤ L →
      T₀ ≤ printedT27 (V := V) (Edges := Edges) L Δ γ (kOf N) := by
  obtain ⟨N₀, hN₀⟩ := generic_entries_eventually_ge T₀
  refine ⟨N₀, ?_⟩
  intro N hN L Δ γ hL
  exact hN₀ N hN L (4 * ell L)
    (CurrentAdditive.RandomizedSchedule.q27 (V := V) (E := Edges) L γ Δ) hL

omit [Nonempty V] in
theorem canonical27_word_eventually_ge (T₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ L Δ : ℕ, ∀ γ : ℚ, 1 ≤ L →
      ∀ bits : List Bool,
      Paper2.AModel.MatrixValid
        (printedRows27 (V := V) (Edges := Edges) L Δ γ (kOf N))
        (printedCols27 (V := V) (Edges := Edges) L Δ γ (kOf N)) bits →
      T₀ ≤ entries (Paper2.AModel.matrixWord
        (printedRows27 (V := V) (Edges := Edges) L Δ γ (kOf N))
        (printedCols27 (V := V) (Edges := Edges) L Δ γ (kOf N)) bits) := by
  obtain ⟨N₀, hN₀⟩ := printedT27_eventually_ge (V := V) (Edges := Edges) T₀
  refine ⟨N₀, ?_⟩
  intro N hN L Δ γ hL bits hvalid
  rw [entries_matrixWord _ _ _ hvalid]
  exact hN₀ N hN L Δ γ hL

#print axioms printedT27_eventually_ge
#print axioms canonical27_word_eventually_ge

end Paper2.CurrentAdditive
