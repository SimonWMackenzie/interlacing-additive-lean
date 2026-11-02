import CurrentAdditive.RandomizedQuarticSchedule

namespace CurrentAdditive.QuarticSchedule

open Paper2

variable {V Edges : Type*} [Fintype V] [Nonempty V] [Fintype Edges]

/-- Explicit source-only size threshold for the literal quartic public check. -/
def threshold27 (Δ : ℕ) (γ : ℚ) : ℕ :=
  2 ^ allCutoff27 Δ γ

theorem cutoff_le_clog_of_threshold27 (Δ : ℕ) (γ : ℚ) (n : ℕ)
    (hsize : threshold27 Δ γ ≤ n) :
    allCutoff27 Δ γ ≤ Nat.clog 2 n := by
  have hc := Nat.clog_mono_right 2 hsize
  simpa only [threshold27, Nat.clog_pow 2
    (allCutoff27 Δ γ) (by decide)] using hc

theorem all_large_checks27_at_graph (edge : Edges → Bool → V)
    (Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hsize : threshold27 Δ γ ≤ Fintype.card V) :
    Checks27 (V := V) (Edges := Edges)
      (Nat.clog 2 (Fintype.card V)) Δ γ := by
  have hcut : allCutoff27 Δ γ ≤ Nat.clog 2 (Fintype.card V) :=
    cutoff_le_clog_of_threshold27 Δ γ _ hsize
  have hcard : Fintype.card V ≤ 2 ^ Nat.clog 2 (Fintype.card V) :=
    Nat.le_pow_clog (by decide) _
  exact all_large_checks27 edge _ Δ γ hcut hγ hΔ hincident hdegree hcard

theorem failure_below_size_threshold27 (edge : Edges → Bool → V)
    (Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hfail : ¬ Checks27 (V := V) (Edges := Edges)
      (Nat.clog 2 (Fintype.card V)) Δ γ) :
    Fintype.card V < threshold27 Δ γ := by
  by_contra h
  exact hfail (all_large_checks27_at_graph edge Δ γ hγ hΔ
    hincident hdegree (Nat.le_of_not_gt h))

#print axioms cutoff_le_clog_of_threshold27
#print axioms all_large_checks27_at_graph
#print axioms failure_below_size_threshold27

end CurrentAdditive.QuarticSchedule
