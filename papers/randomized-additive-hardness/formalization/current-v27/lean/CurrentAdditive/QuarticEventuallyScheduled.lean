import CurrentAdditive.QuarticSourceSize
import CurrentAdditive.QuarticSelectedFiniteGuarantees

namespace Paper2.CurrentAdditive.QuarticConstructor

open CurrentAdditive.QuarticSchedule

/-- A graph above the explicit v27 source-only threshold passes every
literal quartic check at its actual source exponent. -/
theorem checks27_of_large {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hsize : threshold27 Δ γ ≤ n) :
    Checks27 (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hc := all_large_checks27_at_graph (V := Fin n) (Edges := Fin m)
    edge Δ γ hγ hΔ hincident hdegree
    (by simpa only [Fintype.card_fin] using hsize)
  simpa only [Fintype.card_fin] using hc

theorem select27_large_is_scheduled {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hsize : threshold27 Δ γ ≤ n) :
    select27 hn edge Δ γ k =
      scheduledOutput27 hn edge Δ γ k
        (checks27_of_large hn edge Δ γ hγ hΔ hincident hdegree hsize) := by
  exact select27_good hn edge Δ γ k
    (checks27_of_large hn edge Δ γ hγ hΔ hincident hdegree hsize)

theorem experiment27_large_is_scheduled {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hsize : threshold27 Δ γ ≤ n) :
    experiment27 hn edge Δ γ k =
      scheduledExperiment27 hn edge Δ γ k
        (checks27_of_large hn edge Δ γ hγ hΔ hincident hdegree hsize) := by
  have hc := checks27_of_large hn edge Δ γ hγ hΔ
    hincident hdegree hsize
  simp [experiment27, hc]

#print axioms checks27_of_large
#print axioms select27_large_is_scheduled
#print axioms experiment27_large_is_scheduled

end Paper2.CurrentAdditive.QuarticConstructor
