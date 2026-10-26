import CurrentAdditive.QuarticConstructor
import CurrentAdditive.QuarticEntryGrowth

/-! Eventual table-size bound for the actual new scheduled branch, rather than
for an arbitrary dimension-matching word. -/

namespace Paper2.CurrentAdditive.QuarticConstructor

open _root_.CurrentAdditive.Eventual

open SourceRecursiveNoSampling
open Paper2.Unit4Shell.Asymptotics

/-- A fixed threshold is exceeded by the actual canonical v27 word on every
scheduled tape, for all sufficiently large repetition inputs. The cutoff is
uniform in the graph, degree and gap parameters. -/
theorem scheduled27_emitted_eventually_ge (T₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      ∀ {n m : ℕ} (hn : 0 < n)
        (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ)
        (hc : CurrentAdditive.QuarticSchedule.Checks27
          (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
        (t : (scheduledOutput27 hn edge Δ γ (kOf N) hc).Tape),
        T₀ ≤ entries (AModel.matrixWord
          (scheduledOutput27 hn edge Δ γ (kOf N) hc).rows
          (scheduledOutput27 hn edge Δ γ (kOf N) hc).cols
          ((scheduledOutput27 hn edge Δ γ (kOf N) hc).table t).bits) := by
  obtain ⟨N₀, hN₀⟩ := generic_entries_eventually_ge T₀
  refine ⟨N₀, ?_⟩
  intro N hN n m hn edge Δ γ hc t
  rw [entries_matrixWord _ _ _ (scheduled27_valid hn edge Δ γ (kOf N) hc t)]
  change T₀ ≤ sourceRows (Nat.clog 2 n)
      (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n))
      (CurrentAdditive.RandomizedSchedule.q27 (V := Fin n) (E := Fin m)
        (Nat.clog 2 n) γ Δ) (kOf N) *
    sourceCols (Nat.clog 2 n)
      (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n))
      (CurrentAdditive.RandomizedSchedule.q27 (V := Fin n) (E := Fin m)
        (Nat.clog 2 n) γ Δ) (kOf N)
  have hL : 1 ≤ Nat.clog 2 n := by
    have h := hc
    dsimp only [CurrentAdditive.QuarticSchedule.Checks27] at h
    omega
  exact hN₀ N hN (Nat.clog 2 n)
    (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n))
    (CurrentAdditive.RandomizedSchedule.q27 (V := Fin n) (E := Fin m)
      (Nat.clog 2 n) γ Δ) hL

#print axioms scheduled27_emitted_eventually_ge

end Paper2.CurrentAdditive.QuarticConstructor
