import Paper2.PublicScheduleAllLarge

/-! All-large checks at the actual dyadic source parameter, with a finite failure bound. -/

namespace Paper2.CompletePublicScheduleScratch

variable {V E : Type*} [Fintype V] [Nonempty V] [Fintype E]

def sizeThreshold (Δ : ℕ) (γ : ℚ) : ℕ := 2 ^ cutoff Δ γ

theorem all_large_checks_at_graph (edge : E → Bool → V)
    (Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hsize : sizeThreshold Δ γ ≤ Fintype.card V) :
    Checks (V := V) (E := E) (Nat.clog 2 (Fintype.card V)) Δ γ := by
  have hcut : cutoff Δ γ ≤ Nat.clog 2 (Fintype.card V) := by
    have hc := Nat.clog_mono_right 2 hsize
    simpa only [sizeThreshold, Nat.clog_pow 2 (cutoff Δ γ) (by decide)] using hc
  have hcard : Fintype.card V ≤ 2 ^ Nat.clog 2 (Fintype.card V) :=
    Nat.le_pow_clog (by decide) _
  exact all_large_checks edge _ Δ γ hcut hγ hΔ hincident hdegree hcard

theorem failure_below_size_threshold (edge : E → Bool → V)
    (Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hfail : ¬ Checks (V := V) (E := E)
      (Nat.clog 2 (Fintype.card V)) Δ γ) :
    Fintype.card V < sizeThreshold Δ γ := by
  by_contra h
  exact hfail (all_large_checks_at_graph edge Δ γ hγ hΔ hincident hdegree
    (Nat.le_of_not_gt h))


end Paper2.CompletePublicScheduleScratch

