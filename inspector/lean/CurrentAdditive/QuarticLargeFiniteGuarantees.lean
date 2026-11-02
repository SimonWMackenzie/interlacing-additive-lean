import CurrentAdditive.QuarticEventuallyScheduled

namespace Paper2.CurrentAdditive.QuarticConstructor

open CurrentAdditive.QuarticSchedule

/-- Beyond one source-only threshold, the literal public selector is the
quartic scheduled constructor and carries all finite v27 guarantees. -/
theorem large_selected_finite_guarantees27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hk : 1 ≤ k)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m)
    (hsize : threshold27 Δ γ ≤ n) :
    (∃ hc : Checks27 (V := Fin n) (Edges := Fin m)
        (Nat.clog 2 n) Δ γ,
      select27 hn edge Δ γ k = scheduledOutput27 hn edge Δ γ k hc ∧
      experiment27 hn edge Δ γ k = scheduledExperiment27 hn edge Δ γ k hc) ∧
    Guarantees27 hn edge Δ γ k := by
  let hc := checks27_of_large hn edge Δ γ hγ hΔ hincident hdegree hsize
  refine ⟨⟨hc, ?_, ?_⟩, ?_⟩
  · exact select27_good hn edge Δ γ k hc
  · simp [experiment27, hc]
  · exact selected_finite_guarantees27 hn edge Δ γ k hk loopless
      hdegree hγ hΔ hm

theorem eventually_selected_finite_guarantees27
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ) :
    ∃ N : ℕ, ∀ {n m : ℕ} (hn : 0 < n)
      (edge : Fin m → Bool → Fin n) (k : ℕ),
      N ≤ n → 1 ≤ k →
      (∀ e, edge e false ≠ edge e true) →
      (∀ v, ∃ e b, edge e b = v) →
      (∀ v, SourceItems.degree edge v ≤ Δ) →
      0 < m →
      (∃ hc : Checks27 (V := Fin n) (Edges := Fin m)
          (Nat.clog 2 n) Δ γ,
        select27 hn edge Δ γ k = scheduledOutput27 hn edge Δ γ k hc ∧
        experiment27 hn edge Δ γ k = scheduledExperiment27 hn edge Δ γ k hc) ∧
      Guarantees27 hn edge Δ γ k := by
  refine ⟨threshold27 Δ γ, ?_⟩
  intro n m hn edge k hsize hk loopless hincident hdegree hm
  exact large_selected_finite_guarantees27 hn edge Δ γ k hk
    loopless hincident hdegree hγ hΔ hm hsize

#print axioms large_selected_finite_guarantees27
#print axioms eventually_selected_finite_guarantees27

end Paper2.CurrentAdditive.QuarticConstructor
