import CurrentAdditive.QuarticSelectedSuccess

namespace Paper2.CurrentAdditive.QuarticConstructor

open SourceProfileParameters SourceRecursiveNoSampling
  Workspace.Types.CommComplexity

private theorem sourceCost_eq_budget_add27' (L r q k : ℕ) :
    sourceCost L r q k = sourceBudget L r q k + k := by
  simp only [sourceCost, sourceBudget]
  ring

private theorem fallback_cost_le27 {n m : ℕ}
    (edge : Fin m → Bool → Fin n) (k : ℕ) (hk : 1 ≤ k) :
    D (FiniteFallbackOutput.fallbackTable edge k).matrix ≤ k := by
  by_cases hcolour : FiniteFallbackOutput.ThreeColourable edge
  · rw [FiniteFallbackOutput.fallback_yes_D edge k hcolour]
    omega
  · by_cases h1 : k = 1
    · subst k
      rw [FiniteFallbackOutput.fallback_no_one_D edge hcolour]
    · rw [FiniteFallbackOutput.fallback_no_D edge k (by omega) hcolour]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem selected_all_cost_le27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hk : 1 ≤ k)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m) :
    let o := select27 hn edge Δ γ k
    ∀ t : o.Tape, D (o.table t).matrix ≤ o.budget + k := by
  dsimp only
  by_cases hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ
  · letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    rw [select27_good hn edge Δ γ k hc]
    have hG := scheduled_table_finite_guarantees27
      (Nat.clog 2 n) Δ γ edge loopless hdegree hγ hΔ hm hc k
    simpa only [scheduledOutput27, sourceCost_eq_budget_add27'] using hG.1
  · rw [select27_bad hn edge Δ γ k hc]
    simpa [TotalFiniteConstructorScratch.fallbackOutput] using
      (fun (_ : Unit) => fallback_cost_le27 edge k hk)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem selected_yes_cost_le27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m)
    (hcolour : FiniteFallbackOutput.ThreeColourable edge) :
    let o := select27 hn edge Δ γ k
    ∀ t : o.Tape, D (o.table t).matrix ≤ o.budget := by
  dsimp only
  by_cases hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ
  · letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    rw [select27_good hn edge Δ γ k hc]
    have hG := scheduled_table_finite_guarantees27
      (Nat.clog 2 n) Δ γ edge loopless hdegree hγ hΔ hm hc k
    obtain ⟨colour, proper⟩ := hcolour
    simpa only [scheduledOutput27] using hG.2.1 colour proper
  · rw [select27_bad hn edge Δ γ k hc]
    simpa [TotalFiniteConstructorScratch.fallbackOutput,
      FiniteFallbackOutput.budget] using
      (fun (_ : Unit) => Nat.le_of_eq
        (FiniteFallbackOutput.fallback_yes_D edge k hcolour))

#print axioms selected_all_cost_le27
#print axioms selected_yes_cost_le27

end Paper2.CurrentAdditive.QuarticConstructor
