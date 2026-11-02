import CurrentAdditive.QuarticConstructor

/-! The new public check can fail only on a fixed finite source-size range,
provided the graph satisfies the source degree and incidence hypotheses. -/

namespace Paper2.CurrentAdditive.QuarticConstructor

def sizeThreshold27 (Δ : ℕ) (γ : ℚ) : ℕ :=
  2 ^ CurrentAdditive.QuarticSchedule.allCutoff27 Δ γ

theorem all_large_checks27_at_graph {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hsize : sizeThreshold27 Δ γ ≤ n) :
    CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hcut : CurrentAdditive.QuarticSchedule.allCutoff27 Δ γ ≤
      Nat.clog 2 n := by
    have hc := Nat.clog_mono_right 2 hsize
    simpa only [sizeThreshold27,
      Nat.clog_pow 2 (CurrentAdditive.QuarticSchedule.allCutoff27 Δ γ)
        (by decide)] using hc
  have hcard : Fintype.card (Fin n) ≤ 2 ^ Nat.clog 2 n := by
    simpa only [Fintype.card_fin] using
      (Nat.le_pow_clog (by decide : 1 < 2) n)
  exact CurrentAdditive.QuarticSchedule.all_large_checks27 edge
    (Nat.clog 2 n) Δ γ hcut hγ hΔ hincident hdegree hcard

theorem failed_check27_below_threshold {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hfail : ¬ CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ) :
    n < sizeThreshold27 Δ γ := by
  by_contra h
  exact hfail (all_large_checks27_at_graph hn edge Δ γ hγ hΔ hincident
    hdegree (Nat.le_of_not_gt h))

#print axioms failed_check27_below_threshold

end Paper2.CurrentAdditive.QuarticConstructor
